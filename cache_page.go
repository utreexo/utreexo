package utreexo

import "math/bits"

const cachePageSize = 4096 // 4KB per page, matches OS page size

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

type cachePage struct {
	data    [cachePageSize]byte
	present []uint64 // bitmap: 1 bit per slot
	count   int
}

func newPageCacheStore(entrySize int, maxBytes int64) *pageCacheStore {
	if entrySize <= 0 || entrySize > cachePageSize {
		panic("pageCacheStore: entrySize must be in (0, 4096]")
	}
	slotsPerPage := cachePageSize / entrySize
	wordsPerPage := (slotsPerPage + 63) / 64

	return &pageCacheStore{
		pages:        make(map[int64]*cachePage),
		entrySize_:   entrySize,
		slotsPerPage: slotsPerPage,
		wordsPerPage: wordsPerPage,
		maxEntries:   int(maxBytes) / entrySize,
	}
}

func (p *pageCacheStore) entrySize() int { return p.entrySize_ }

func (p *pageCacheStore) pageAndSlot(offset int64) (pageNum int64, slot int) {
	pageNum = offset / cachePageSize
	slot = int(offset%cachePageSize) / p.entrySize_
	return
}

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

func (pg *cachePage) isPresent(slot int) bool {
	return pg.present[slot/64]>>(uint(slot)%64)&1 != 0
}

func (pg *cachePage) setPresent(slot int) {
	pg.present[slot/64] |= 1 << (uint(slot) % 64)
}

func (pg *cachePage) clearPresent(slot int) {
	pg.present[slot/64] &^= 1 << (uint(slot) % 64)
}

func (p *pageCacheStore) get(offset int64) ([]byte, bool) {
	pageNum, slot := p.pageAndSlot(offset)
	pg := p.pages[pageNum]
	if pg == nil || !pg.isPresent(slot) {
		return nil, false
	}
	start := slot * p.entrySize_
	return pg.data[start : start+p.entrySize_], true
}

func (p *pageCacheStore) put(offset int64, data []byte) {
	pageNum, slot := p.pageAndSlot(offset)
	pg := p.getPage(pageNum)
	start := slot * p.entrySize_
	copy(pg.data[start:start+p.entrySize_], data)
	if !pg.isPresent(slot) {
		pg.setPresent(slot)
		pg.count++
		p.totalCount++
	}
}

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

func (p *pageCacheStore) clear() {
	clear(p.pages)
	p.totalCount = 0
}

func (p *pageCacheStore) forEach(fn func(offset int64, data []byte)) {
	for pageNum, pg := range p.pages {
		baseOffset := pageNum * cachePageSize
		for w, word := range pg.present {
			for word != 0 {
				bit := bits.TrailingZeros64(word)
				slot := w*64 + bit
				start := slot * p.entrySize_
				fn(baseOffset+int64(start), pg.data[start:start+p.entrySize_])
				word &= word - 1 // clear lowest set bit
			}
		}
	}
}

func (p *pageCacheStore) overflowed() bool {
	return p.totalCount > p.maxEntries
}

func (p *pageCacheStore) count() int {
	return p.totalCount
}
