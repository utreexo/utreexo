package utreexo

import "math/bits"

const mmapSegmentSize = 1 << 20 // 1MB per segment

// mmapCacheStore implements cacheStore using anonymous mmap segments.
// Each segment is a 1MB region allocated via mmap (MAP_ANONYMOUS on unix,
// byte slice fallback elsewhere). Data lives outside the Go heap, avoiding
// GC scanning overhead. A bitmap per segment tracks which slots are occupied.
type mmapCacheStore struct {
	segments     map[int64]*mmapSegment
	entrySize_   int
	slotsPerSeg  int
	wordsPerSeg  int // bitmap uint64 words needed per segment
	maxEntries   int
	totalCount   int
}

type mmapSegment struct {
	data    []byte   // mmap'd anonymous region (or byte slice on non-unix)
	present []uint64 // bitmap: 1 bit per slot
	count   int
}

func newMmapCacheStore(entrySize int, maxBytes int64) *mmapCacheStore {
	if entrySize <= 0 || entrySize > mmapSegmentSize {
		panic("mmapCacheStore: entrySize must be in (0, 1048576]")
	}
	slotsPerSeg := mmapSegmentSize / entrySize
	wordsPerSeg := (slotsPerSeg + 63) / 64

	return &mmapCacheStore{
		segments:    make(map[int64]*mmapSegment),
		entrySize_:  entrySize,
		slotsPerSeg: slotsPerSeg,
		wordsPerSeg: wordsPerSeg,
		maxEntries:  int(maxBytes) / entrySize,
	}
}

func (m *mmapCacheStore) entrySize() int { return m.entrySize_ }

func (m *mmapCacheStore) segAndSlot(offset int64) (segNum int64, slot int) {
	segNum = offset / mmapSegmentSize
	slot = int(offset%mmapSegmentSize) / m.entrySize_
	return
}

func (m *mmapCacheStore) getSeg(segNum int64) *mmapSegment {
	seg := m.segments[segNum]
	if seg == nil {
		data, err := mmapAnon(mmapSegmentSize)
		if err != nil {
			// Should not happen for anonymous mappings on any reasonable
			// system. Panic is appropriate here; callers can't handle a
			// cache allocation failure gracefully.
			panic("mmapCacheStore: " + err.Error())
		}
		seg = &mmapSegment{
			data:    data,
			present: make([]uint64, m.wordsPerSeg),
		}
		m.segments[segNum] = seg
	}
	return seg
}

func (seg *mmapSegment) isPresent(slot int) bool {
	return seg.present[slot/64]>>(uint(slot)%64)&1 != 0
}

func (seg *mmapSegment) setPresent(slot int) {
	seg.present[slot/64] |= 1 << (uint(slot) % 64)
}

func (seg *mmapSegment) clearPresent(slot int) {
	seg.present[slot/64] &^= 1 << (uint(slot) % 64)
}

func (m *mmapCacheStore) get(offset int64) ([]byte, bool) {
	segNum, slot := m.segAndSlot(offset)
	seg := m.segments[segNum]
	if seg == nil || !seg.isPresent(slot) {
		return nil, false
	}
	start := slot * m.entrySize_
	return seg.data[start : start+m.entrySize_], true
}

func (m *mmapCacheStore) put(offset int64, data []byte) {
	segNum, slot := m.segAndSlot(offset)
	seg := m.getSeg(segNum)
	start := slot * m.entrySize_
	copy(seg.data[start:start+m.entrySize_], data)
	if !seg.isPresent(slot) {
		seg.setPresent(slot)
		seg.count++
		m.totalCount++
	}
}

func (m *mmapCacheStore) delete(offset int64) {
	segNum, slot := m.segAndSlot(offset)
	seg := m.segments[segNum]
	if seg == nil || !seg.isPresent(slot) {
		return
	}
	seg.clearPresent(slot)
	seg.count--
	m.totalCount--
	if seg.count == 0 {
		mmapRelease(seg.data)
		delete(m.segments, segNum)
	}
}

func (m *mmapCacheStore) deleteAbove(size int64) {
	boundarySeg := size / mmapSegmentSize
	for segNum, seg := range m.segments {
		if segNum > boundarySeg {
			m.totalCount -= seg.count
			mmapRelease(seg.data)
			delete(m.segments, segNum)
		} else if segNum == boundarySeg {
			boundarySlot := int(size%mmapSegmentSize) / m.entrySize_
			for slot := boundarySlot; slot < m.slotsPerSeg; slot++ {
				if seg.isPresent(slot) {
					seg.clearPresent(slot)
					seg.count--
					m.totalCount--
				}
			}
			if seg.count == 0 {
				mmapRelease(seg.data)
				delete(m.segments, segNum)
			}
		}
	}
}

func (m *mmapCacheStore) clear() {
	for _, seg := range m.segments {
		mmapRelease(seg.data)
	}
	clear(m.segments)
	m.totalCount = 0
}

func (m *mmapCacheStore) forEach(fn func(offset int64, data []byte)) {
	for segNum, seg := range m.segments {
		baseOffset := segNum * mmapSegmentSize
		for w, word := range seg.present {
			for word != 0 {
				bit := bits.TrailingZeros64(word)
				slot := w*64 + bit
				start := slot * m.entrySize_
				fn(baseOffset+int64(start), seg.data[start:start+m.entrySize_])
				word &= word - 1 // clear lowest set bit
			}
		}
	}
}

func (m *mmapCacheStore) overflowed() bool {
	return m.totalCount > m.maxEntries
}

func (m *mmapCacheStore) count() int {
	return m.totalCount
}
