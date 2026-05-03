// Package mmapcache provides a cache backed by a single anonymous mmap region.
// The region covers the full data file address space but pages are
// demand-paged by the kernel, so only touched pages consume physical memory.
// A separate presence bitmap tracks which slots have cached data (for Get).
// A separate dirty bitmap tracks which slots were written since the last
// ClearDirty (for ForEach). [min,max] ranges over each bitmap bound the
// scan so iteration cost stays proportional to live data, not to the
// virtual address space.
package mmapcache

import (
	"encoding/binary"
	"fmt"
	"math"
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
//
// Two parallel bitmaps cover the slot space:
//   - bitmap: presence — set when a slot has cached data (read by Get).
//   - dirtyBitmap: dirty — set on Put, cleared by ClearDirty (read by ForEach).
//
// Dirty bits are always a subset of presence bits, so a presence-range
// scan dominates a dirty-range scan.
type Store struct {
	data        []byte // mmap'd data region (demand-paged)
	bitmap      []byte // mmap'd presence bitmap; tracks which slots have cached data for Get
	dirtyBitmap []byte // mmap'd dirty bitmap; tracks which slots were written since last ClearDirty

	entrySize  int
	slots      int // total number of slots
	words      int // number of uint64 words in each bitmap
	maxEntries int
	totalCount int // count of dirty bits

	// Inclusive range of dirty bitmap word indices that may have set bits.
	// ForEach and ClearDirty scan only this range.
	dirtyMinWord int
	dirtyMaxWord int

	// Inclusive range of presence bitmap word indices that may have set
	// bits. Clear and DeleteAbove scan only this range.
	presMinWord int
	presMaxWord int
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
	dirtyBitmap, err := mmapAnon(bitmapSize)
	if err != nil {
		mmapRelease(data)
		mmapRelease(bitmap)
		return nil, fmt.Errorf("mmapcache: mmap dirtyBitmap %d bytes: %w", bitmapSize, err)
	}

	return &Store{
		data:         data,
		bitmap:       bitmap,
		dirtyBitmap:  dirtyBitmap,
		entrySize:    entrySize,
		slots:        slots,
		words:        words,
		maxEntries:   int(maxBytes) / entrySize,
		dirtyMinWord: math.MaxInt,
		dirtyMaxWord: -1,
		presMinWord:  math.MaxInt,
		presMaxWord:  -1,
	}, nil
}

// EntrySize returns the fixed size of each entry in bytes.
func (s *Store) EntrySize() int { return s.entrySize }

// wordAt reads the w-th uint64 from the given bitmap.
func wordAt(bm []byte, w int) uint64 {
	return binary.LittleEndian.Uint64(bm[w*8:])
}

// setWordAt writes the w-th uint64 in the given bitmap.
func setWordAt(bm []byte, w int, v uint64) {
	binary.LittleEndian.PutUint64(bm[w*8:], v)
}

// extendDirtyRange widens [dirtyMinWord, dirtyMaxWord] to include w.
func (s *Store) extendDirtyRange(w int) {
	if w < s.dirtyMinWord {
		s.dirtyMinWord = w
	}
	if w > s.dirtyMaxWord {
		s.dirtyMaxWord = w
	}
}

// extendPresRange widens [presMinWord, presMaxWord] to include w.
func (s *Store) extendPresRange(w int) {
	if w < s.presMinWord {
		s.presMinWord = w
	}
	if w > s.presMaxWord {
		s.presMaxWord = w
	}
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
	if wordAt(s.bitmap, w)>>bit&1 == 0 {
		return nil, false
	}
	start := slot * s.entrySize
	return s.data[start : start+s.entrySize], true
}

// Put stores data at the given byte offset. len(data) must equal EntrySize().
func (s *Store) Put(offset int64, data []byte) error {
	if len(data) != s.entrySize {
		return fmt.Errorf("mmapcache: Put: len(data)=%d, want %d", len(data), s.entrySize)
	}
	slot := int(offset) / s.entrySize
	start := slot * s.entrySize
	copy(s.data[start:start+s.entrySize], data)
	w, bit := slot/bitsPerWord, uint(slot)%bitsPerWord
	mask := uint64(1) << bit

	// Set presence bit (read by Get for cache hits).
	if presWord := wordAt(s.bitmap, w); presWord&mask == 0 {
		setWordAt(s.bitmap, w, presWord|mask)
		s.extendPresRange(w)
	}
	// Set dirty bit (read by ForEach for flush iteration).
	if dirtyWord := wordAt(s.dirtyBitmap, w); dirtyWord&mask == 0 {
		setWordAt(s.dirtyBitmap, w, dirtyWord|mask)
		s.extendDirtyRange(w)
		s.totalCount++
	}
	return nil
}

// Delete removes the entry at the given byte offset.
func (s *Store) Delete(offset int64) {
	slot := int(offset) / s.entrySize
	w, bit := slot/bitsPerWord, uint(slot)%bitsPerWord
	mask := uint64(1) << bit

	// Clear presence bit.
	if presWord := wordAt(s.bitmap, w); presWord&mask != 0 {
		setWordAt(s.bitmap, w, presWord&^mask)
	}
	// Clear dirty bit and adjust count.
	if dirtyWord := wordAt(s.dirtyBitmap, w); dirtyWord&mask != 0 {
		setWordAt(s.dirtyBitmap, w, dirtyWord&^mask)
		s.totalCount--
	}
}

// DeleteAbove removes all entries at offsets >= size (used for truncation).
//
// Iterates the presence range, which is a superset of the dirty range
// (dirty ⊆ presence is invariant), so a single pass clears both bitmaps.
func (s *Store) DeleteAbove(size int64) {
	startSlot := int(size) / s.entrySize
	startWord := startSlot / bitsPerWord

	lo := s.presMinWord
	hi := s.presMaxWord
	if lo > hi {
		return
	}
	if startWord > lo {
		lo = startWord
	}
	for w := lo; w <= hi; w++ {
		var keepMask uint64
		if w == startWord {
			// Keep bits below startSlot within this word.
			keepBits := uint(startSlot) % bitsPerWord
			keepMask = (1 << keepBits) - 1
		}
		if presWord := wordAt(s.bitmap, w); presWord != 0 {
			setWordAt(s.bitmap, w, presWord&keepMask)
		}
		if dirtyWord := wordAt(s.dirtyBitmap, w); dirtyWord != 0 {
			cleared := bits.OnesCount64(dirtyWord) - bits.OnesCount64(dirtyWord&keepMask)
			setWordAt(s.dirtyBitmap, w, dirtyWord&keepMask)
			s.totalCount -= cleared
		}
	}
}

// Clear removes all entries. The mmap regions remain allocated so the
// store can be reused without re-mapping.
func (s *Store) Clear() {
	for w := s.presMinWord; w <= s.presMaxWord; w++ {
		if wordAt(s.bitmap, w) != 0 {
			setWordAt(s.bitmap, w, 0)
		}
	}
	for w := s.dirtyMinWord; w <= s.dirtyMaxWord; w++ {
		if wordAt(s.dirtyBitmap, w) != 0 {
			setWordAt(s.dirtyBitmap, w, 0)
		}
	}
	s.totalCount = 0
	s.dirtyMinWord = math.MaxInt
	s.dirtyMaxWord = -1
	s.presMinWord = math.MaxInt
	s.presMaxWord = -1
}

// ClearDirty resets the dirty tracking but keeps all cached entries
// readable (presence bitmap and data are preserved). After ClearDirty,
// ForEach iterates nothing until subsequent Puts dirty new bits.
func (s *Store) ClearDirty() {
	for w := s.dirtyMinWord; w <= s.dirtyMaxWord; w++ {
		if wordAt(s.dirtyBitmap, w) != 0 {
			setWordAt(s.dirtyBitmap, w, 0)
		}
	}
	s.totalCount = 0
	s.dirtyMinWord = math.MaxInt
	s.dirtyMaxWord = -1
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
	if s.dirtyBitmap != nil {
		mmapRelease(s.dirtyBitmap)
		s.dirtyBitmap = nil
	}
	s.totalCount = 0
}

// ForEach iterates over all dirty entries (written since last ClearDirty),
// calling fn for each one.
func (s *Store) ForEach(fn func(offset int64, data []byte)) {
	for w := s.dirtyMinWord; w <= s.dirtyMaxWord; w++ {
		word := wordAt(s.dirtyBitmap, w)
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

// Count returns the total number of dirty entries.
func (s *Store) Count() int { return s.totalCount }
