// Package mmapcache provides a cache backed by a single anonymous mmap
// region. Data is indexed directly by file offset — no intermediate map
// lookups. The region grows via mremap as higher offsets are seen.
// Physical pages are only allocated on first write (demand-paged), so
// the virtual reservation is cheap. Linux-only.
package mmapcache

import "math/bits"

const initialDataSize = 1 << 20 // 1MB initial mmap

// Store is an mmap-backed cache for fixed-size entries.
type Store struct {
	data       []byte   // single anonymous mmap region
	present    []uint64 // bitmap: 1 bit per slot
	entrySize  int
	slots      int // total slots in current allocation
	maxEntries int
	totalCount int
}

// New creates a Store for entries of the given byte size.
// maxBytes sets the threshold for signaling that a flush is needed.
func New(entrySize int, maxBytes int64) *Store {
	if entrySize <= 0 {
		panic("mmapcache: entrySize must be positive")
	}
	data, err := mmapAnon(initialDataSize)
	if err != nil {
		panic("mmapcache: " + err.Error())
	}
	slots := initialDataSize / entrySize
	return &Store{
		data:       data,
		present:    make([]uint64, (slots+63)/64),
		entrySize:  entrySize,
		slots:      slots,
		maxEntries: int(maxBytes) / entrySize,
	}
}

func (s *Store) EntrySize() int { return s.entrySize }

// ensureCapacity grows the mmap region via mremap if offset is beyond
// the current allocation.
func (s *Store) ensureCapacity(offset int64) {
	needed := int(offset) + s.entrySize
	if needed <= len(s.data) {
		return
	}
	newSize := len(s.data)
	for newSize < needed {
		newSize *= 2
	}
	newData, err := mmapGrow(s.data, newSize)
	if err != nil {
		panic("mmapcache: grow: " + err.Error())
	}
	s.data = newData
	s.slots = newSize / s.entrySize

	newWords := (s.slots + 63) / 64
	if newWords > len(s.present) {
		grown := make([]uint64, newWords)
		copy(grown, s.present)
		s.present = grown
	}
}

func (s *Store) Get(offset int64) ([]byte, bool) {
	slot := int(offset) / s.entrySize
	if slot >= s.slots {
		return nil, false
	}
	if s.present[slot/64]>>(uint(slot)%64)&1 == 0 {
		return nil, false
	}
	start := int(offset)
	return s.data[start : start+s.entrySize], true
}

func (s *Store) Put(offset int64, data []byte) {
	s.ensureCapacity(offset)
	slot := int(offset) / s.entrySize
	start := int(offset)
	copy(s.data[start:start+s.entrySize], data)
	if s.present[slot/64]>>(uint(slot)%64)&1 == 0 {
		s.present[slot/64] |= 1 << (uint(slot) % 64)
		s.totalCount++
	}
}

func (s *Store) Delete(offset int64) {
	slot := int(offset) / s.entrySize
	if slot >= s.slots {
		return
	}
	w := slot / 64
	mask := uint64(1) << (uint(slot) % 64)
	if s.present[w]&mask != 0 {
		s.present[w] &^= mask
		s.totalCount--
	}
}

func (s *Store) DeleteAbove(size int64) {
	boundarySlot := int(size) / s.entrySize
	if boundarySlot >= s.slots {
		return
	}

	startWord := boundarySlot / 64
	bitInWord := uint(boundarySlot) % 64

	// Handle partial first word: clear bits from bitInWord to 63.
	if bitInWord > 0 {
		mask := ^uint64(0) << bitInWord
		cleared := s.present[startWord] & mask
		s.totalCount -= bits.OnesCount64(cleared)
		s.present[startWord] &^= mask
		startWord++
	}

	// Clear remaining full words.
	for w := startWord; w < len(s.present); w++ {
		s.totalCount -= bits.OnesCount64(s.present[w])
		s.present[w] = 0
	}
}

func (s *Store) Clear() {
	newData, err := mmapReplace(s.data)
	if err != nil {
		panic("mmapcache: clear: " + err.Error())
	}
	s.data = newData
	for i := range s.present {
		s.present[i] = 0
	}
	s.totalCount = 0
}

func (s *Store) ForEach(fn func(offset int64, data []byte)) {
	for w, word := range s.present {
		for word != 0 {
			bit := bits.TrailingZeros64(word)
			slot := w*64 + bit
			start := slot * s.entrySize
			fn(int64(start), s.data[start:start+s.entrySize])
			word &= word - 1
		}
	}
}

func (s *Store) Overflowed() bool { return s.totalCount > s.maxEntries }
func (s *Store) Count() int       { return s.totalCount }
