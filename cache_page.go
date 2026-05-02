package utreexo

import "math/bits"

const (
	cachePageSize = 4096 // 4KB per page, matches OS page size
	bitsPerWord   = 64   // bits in a uint64 bitmap word
)

// cachePage is a fixed-size page that stores cache entries as slots within a
// contiguous byte array. A bitmap tracks which slots are occupied, allowing
// direct lookup, insert, and delete by slot index without per-entry map overhead.
type cachePage struct {
	data    [cachePageSize]byte
	present []uint64 // bitmap: 1 bit per slot
	count   int
}

// isPresent returns true if the given slot has data in the bitmap.
func (pg *cachePage) isPresent(slot int) bool {
	return pg.present[slot/bitsPerWord]>>(uint(slot)%bitsPerWord)&1 != 0
}

// setPresent marks the given slot as occupied in the bitmap.
func (pg *cachePage) setPresent(slot int) {
	pg.present[slot/bitsPerWord] |= 1 << (uint(slot) % bitsPerWord)
}

// clearPresent marks the given slot as empty in the bitmap.
func (pg *cachePage) clearPresent(slot int) {
	pg.present[slot/bitsPerWord] &^= 1 << (uint(slot) % bitsPerWord)
}

// pageCacheStore implements cacheStore using fixed-size pages indexed by
// page number. Within each page, entries are accessed by direct array
// indexing with a bitmap tracking which slots are occupied.
//
// This amortizes the Go map overhead across many entries per page
// (e.g. 128 entries per page for 32-byte records) instead of one map
// entry per cached record.
type pageCacheStore struct {
	pages        map[int64]*cachePage
	entrySize_   int
	slotsPerPage int
	wordsPerPage int // bitmap uint64 words needed per page
	maxEntries   int
	totalCount   int
}

// newPageCacheStore creates a pageCacheStore for entries of the given byte
// size. maxBytes sets the threshold for signaling that a flush is needed.
func newPageCacheStore(entrySize int, maxBytes int64) *pageCacheStore {
	if entrySize <= 0 || entrySize > cachePageSize {
		panic("pageCacheStore: entrySize must be in (0, 4096]")
	}
	slotsPerPage := cachePageSize / entrySize
	wordsPerPage := (slotsPerPage + bitsPerWord - 1) / bitsPerWord

	return &pageCacheStore{
		pages:        make(map[int64]*cachePage),
		entrySize_:   entrySize,
		slotsPerPage: slotsPerPage,
		wordsPerPage: wordsPerPage,
		maxEntries:   int(maxBytes) / entrySize,
	}
}

func (p *pageCacheStore) entrySize() int { return p.entrySize_ }

// pageAndSlot converts a byte offset into the page number and the slot
// index within that page.
func (p *pageCacheStore) pageAndSlot(offset int64) (pageNum int64, slot int) {
	pageNum = offset / cachePageSize
	slot = int(offset%cachePageSize) / p.entrySize_
	return
}

// getPage returns the page for pageNum, allocating it if it doesn't exist.
func (p *pageCacheStore) getPage(pageNum int64) *cachePage {
	pg := p.pages[pageNum]
	if pg == nil {
		pg = &cachePage{
			present: make([]uint64, p.wordsPerPage),
		}
		p.pages[pageNum] = pg
	}
	return pg
}

// get returns the cached entry at the given byte offset, or false if not present.
// The returned slice aliases the page's internal storage.
func (p *pageCacheStore) get(offset int64) ([]byte, bool) {
	pageNum, slot := p.pageAndSlot(offset)
	pg := p.pages[pageNum]
	if pg == nil || !pg.isPresent(slot) {
		return nil, false
	}
	start := slot * p.entrySize_
	return pg.data[start : start+p.entrySize_], true
}

// put writes data into the cache at the given byte offset, allocating a page if needed.
func (p *pageCacheStore) put(offset int64, data []byte) error {
	pageNum, slot := p.pageAndSlot(offset)
	pg := p.getPage(pageNum)
	start := slot * p.entrySize_
	copy(pg.data[start:start+p.entrySize_], data)
	if !pg.isPresent(slot) {
		pg.setPresent(slot)
		pg.count++
		p.totalCount++
	}
	return nil
}

// delete removes the cached entry at the given byte offset. If the page becomes
// empty, it is freed from the map.
func (p *pageCacheStore) delete(offset int64) {
	pageNum, slot := p.pageAndSlot(offset)
	pg := p.pages[pageNum]
	if pg == nil || !pg.isPresent(slot) {
		return
	}
	pg.clearPresent(slot)
	pg.count--
	p.totalCount--
	if pg.count == 0 {
		delete(p.pages, pageNum)
	}
}

// deleteAbove removes all cached entries at byte offsets >= size.
func (p *pageCacheStore) deleteAbove(size int64) {
	boundaryPage := size / cachePageSize
	for pageNum, pg := range p.pages {
		if pageNum > boundaryPage {
			p.totalCount -= pg.count
			delete(p.pages, pageNum)
		} else if pageNum == boundaryPage {
			// Clear slots at offsets >= size within the boundary page.
			boundarySlot := int(size%cachePageSize) / p.entrySize_
			for slot := boundarySlot; slot < p.slotsPerPage; slot++ {
				if pg.isPresent(slot) {
					pg.clearPresent(slot)
					pg.count--
					p.totalCount--
				}
			}
			if pg.count == 0 {
				delete(p.pages, pageNum)
			}
		}
	}
}

// clear removes all cached entries and frees all pages.
func (p *pageCacheStore) clear() {
	clear(p.pages)
	p.totalCount = 0
}

// clearDirty is a no-op for pageCacheStore since it doesn't have separate
// dirty tracking — falls back to full clear.
func (p *pageCacheStore) clearDirty() {
	p.clear()
}

// forEach iterates over all occupied slots, calling fn with the byte offset and
// data for each cached entry.
func (p *pageCacheStore) forEach(fn func(offset int64, data []byte)) {
	for pageNum, pg := range p.pages {
		baseOffset := pageNum * cachePageSize
		for w, word := range pg.present {
			for word != 0 {
				bit := bits.TrailingZeros64(word)
				slot := w*bitsPerWord + bit
				start := slot * p.entrySize_
				fn(baseOffset+int64(start), pg.data[start:start+p.entrySize_])
				word &= word - 1 // clear lowest set bit
			}
		}
	}
}

// overflowed returns true if the total number of cached entries exceeds the
// configured maximum, signaling that a flush is needed.
func (p *pageCacheStore) overflowed() bool {
	return p.totalCount > p.maxEntries
}

// count returns the total number of cached entries across all pages.
func (p *pageCacheStore) count() int {
	return p.totalCount
}

// close is a no-op for the page-based cache (no external resources to release).
func (p *pageCacheStore) close() {}
