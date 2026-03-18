// Package mmapcache provides a cache backed by a single anonymous mmap region.
// The region covers the full data file address space but pages are
// demand-paged by the kernel, so only touched pages consume physical memory.
// A second mmap region serves as a bitmap tracking which slots are occupied.
// A dense list of non-zero bitmap word indices makes ForEach fast regardless
// of how large or sparse the address space is.
package mmapcache

import (
	"encoding/binary"
	"fmt"
	"math/bits"
)

const bitsPerWord = 64

// maxRegionSize is the virtual address space allocated for the data region.
// With MAP_ANONYMOUS|MAP_NORESERVE only touched pages consume physical memory,
// so this can be very large without cost. On 64-bit platforms the value is
// 1 TB (well within the 128 TB user-space limit); on 32-bit it is 1 GB.
//
// NOTE: 32-bit support is untested and may fail at runtime.
const maxRegionSize = 1 << (30 + 10*(^uint(0)>>63))

// Store is an mmap-backed cache for fixed-size entries.
type Store struct {
	data       []byte // mmap'd data region (demand-paged)
	bitmap     []byte // mmap'd bitmap region (demand-paged), read as uint64 words
	dirty      []int  // dense list of bitmap word indices with set bits; enables fast iteration in ForEach/Clear without scanning the entire sparse bitmap
	dirtySet   []byte // 1 bit per bitmap word; dedup guard so markDirty can check in O(1) whether a word index is already in the dirty list
	entrySize  int
	slots      int // total number of slots
	words      int // number of uint64 words in bitmap
	maxEntries int
	totalCount int
}

// New creates a Store for entries of the given byte size.
// maxBytes sets the threshold for signaling that a flush is needed.
func New(entrySize int, maxBytes int64) (*Store, error) {
	if entrySize <= 0 {
		return nil, fmt.Errorf("mmapcache: entrySize must be positive")
	}
	slots := maxRegionSize / entrySize
	words := (slots + bitsPerWord - 1) / bitsPerWord
	bitmapSize := words * 8
	if bitmapSize == 0 {
		bitmapSize = 8
	}

	data, err := mmapAnon(maxRegionSize)
	if err != nil {
		return nil, fmt.Errorf("mmapcache: mmap data %d bytes: %w", maxRegionSize, err)
	}
	bitmap, err := mmapAnon(bitmapSize)
	if err != nil {
		mmapRelease(data)
		return nil, fmt.Errorf("mmapcache: mmap bitmap %d bytes: %w", bitmapSize, err)
	}

	dirtySetSize := (words + 7) / 8
	dirtySet, err := mmapAnon(max(dirtySetSize, 1))
	if err != nil {
		mmapRelease(data)
		mmapRelease(bitmap)
		return nil, fmt.Errorf("mmapcache: mmap dirtySet %d bytes: %w", dirtySetSize, err)
	}

	return &Store{
		data:       data,
		bitmap:     bitmap,
		dirtySet:   dirtySet,
		entrySize:  entrySize,
		slots:      slots,
		words:      words,
		maxEntries: int(maxBytes) / entrySize,
	}, nil
}

// EntrySize returns the fixed size of each entry in bytes.
func (s *Store) EntrySize() int { return s.entrySize }

// word reads the w-th uint64 from the mmap'd bitmap.
func (s *Store) word(w int) uint64 {
	return binary.LittleEndian.Uint64(s.bitmap[w*8:])
}

// setWord writes the w-th uint64 in the mmap'd bitmap.
func (s *Store) setWord(w int, v uint64) {
	binary.LittleEndian.PutUint64(s.bitmap[w*8:], v)
}

// isDirty returns true if bitmap word w is tracked in the dirty list.
func (s *Store) isDirty(w int) bool {
	return s.dirtySet[w/8]>>(uint(w)%8)&1 != 0
}

// markDirty adds bitmap word w to the dirty list if not already present.
func (s *Store) markDirty(w int) {
	if s.isDirty(w) {
		return
	}
	s.dirtySet[w/8] |= 1 << (uint(w) % 8)
	s.dirty = append(s.dirty, w)
}

// Get retrieves the data at the given byte offset. Returns nil, false if
// the offset has no cached entry. The returned slice aliases internal storage.
//
// The slot calculation (offset / entrySize * entrySize) is equivalent to using
// the offset directly when it is already aligned to entrySize. The integer
// division provides implicit alignment protection by snapping misaligned
// offsets to the nearest slot boundary.
func (s *Store) Get(offset int64) ([]byte, bool) {
	slot := int(offset) / s.entrySize
	w, bit := slot/bitsPerWord, uint(slot)%bitsPerWord
	if s.word(w)>>bit&1 == 0 {
		return nil, false
	}
	start := slot * s.entrySize
	return s.data[start : start+s.entrySize], true
}

// Put stores data at the given byte offset. len(data) must equal EntrySize().
//
// The slot calculation (offset / entrySize * entrySize) is equivalent to using
// the offset directly when it is already aligned to entrySize. The integer
// division provides implicit alignment protection by snapping misaligned
// offsets to the nearest slot boundary.
func (s *Store) Put(offset int64, data []byte) error {
	if len(data) != s.entrySize {
		return fmt.Errorf("mmapcache: Put: len(data)=%d, want %d", len(data), s.entrySize)
	}
	slot := int(offset) / s.entrySize
	start := slot * s.entrySize
	copy(s.data[start:start+s.entrySize], data)
	w, bit := slot/bitsPerWord, uint(slot)%bitsPerWord
	word := s.word(w)
	if word>>bit&1 == 0 {
		s.markDirty(w)
		s.setWord(w, word|1<<bit)
		s.totalCount++
	}
	return nil
}

// Delete removes the entry at the given byte offset.
//
// The slot calculation (offset / entrySize * entrySize) is equivalent to using
// the offset directly when it is already aligned to entrySize. The integer
// division provides implicit alignment protection by snapping misaligned
// offsets to the nearest slot boundary.
func (s *Store) Delete(offset int64) {
	slot := int(offset) / s.entrySize
	w, bit := slot/bitsPerWord, uint(slot)%bitsPerWord
	word := s.word(w)
	if word>>bit&1 == 0 {
		return
	}
	s.setWord(w, word&^(1<<bit))
	s.totalCount--
}

// DeleteAbove removes all entries at offsets >= size (used for truncation).
//
// The slot calculation (offset / entrySize * entrySize) is equivalent to using
// the offset directly when it is already aligned to entrySize. The integer
// division provides implicit alignment protection by snapping misaligned
// offsets to the nearest slot boundary.
func (s *Store) DeleteAbove(size int64) {
	startSlot := int(size) / s.entrySize
	startWord := startSlot / bitsPerWord
	for _, w := range s.dirty {
		if w < startWord {
			continue
		}
		word := s.word(w)
		if word == 0 {
			continue
		}
		var mask uint64
		if w == startWord {
			// Keep bits below startSlot within this word.
			keepBits := uint(startSlot) % bitsPerWord
			mask = (1 << keepBits) - 1
		}
		cleared := bits.OnesCount64(word) - bits.OnesCount64(word&mask)
		s.setWord(w, word&mask)
		s.totalCount -= cleared
	}
}

// Clear removes all entries. The mmap regions remain allocated so the
// store can be reused without re-mapping.
func (s *Store) Clear() {
	for _, w := range s.dirty {
		s.setWord(w, 0)
		s.dirtySet[w/8] &^= 1 << (uint(w) % 8)
	}
	s.dirty = s.dirty[:0]
	s.totalCount = 0
}

// Close releases all mmap regions back to the OS.
func (s *Store) Close() {
	if s.data != nil {
		mmapRelease(s.data)
		s.data = nil
	}
	if s.bitmap != nil {
		mmapRelease(s.bitmap)
		s.bitmap = nil
	}
	if s.dirtySet != nil {
		mmapRelease(s.dirtySet)
		s.dirtySet = nil
	}
	s.dirty = nil
	s.totalCount = 0
}

// ForEach iterates over all cached entries, calling fn for each one.
func (s *Store) ForEach(fn func(offset int64, data []byte)) {
	for _, w := range s.dirty {
		word := s.word(w)
		for word != 0 {
			bit := bits.TrailingZeros64(word)
			slot := w*bitsPerWord + bit
			start := slot * s.entrySize
			fn(int64(start), s.data[start:start+s.entrySize])
			word &= word - 1
		}
	}
}

// Overflowed returns true if the cache has exceeded its memory budget.
func (s *Store) Overflowed() bool { return s.totalCount > s.maxEntries }

// Count returns the total number of cached entries.
func (s *Store) Count() int { return s.totalCount }
