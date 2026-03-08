package utreexo

import "github.com/utreexo/utreexo/internal/sizehelper"

const (
	// defaultMaxCacheMemory is 64MB per cachedRWS.
	defaultMaxCacheMemory = 64 << 20
)

// cacheStore is the interface for underlying cache storage.
type cacheStore interface {
	// get retrieves the data at the given offset. Returns false if not found.
	get(offset int64) ([]byte, bool)

	// delete removes the entry at the given offset.
	delete(offset int64)

	// deleteAbove removes all entries at offsets >= size (used for truncation).
	deleteAbove(size int64)

	// clear removes all entries from the cache.
	clear()

	// forEach iterates over all cached entries, calling fn for each.
	forEach(fn func(offset int64, data []byte))

	// overflowed returns true if entries have spilled into the overflow map,
	// indicating the cache has exceeded its memory budget.
	overflowed() bool

	// count returns the total number of cached entries.
	count() int

	// entrySize returns the fixed size of each entry in bytes (4, 8, or 32).
	entrySize() int
}

// cacheMap32 stores 32-byte entries (hashes).
type cacheMap32 struct {
	maps       []map[int64][32]byte
	overflow   map[int64][32]byte
	maxEntries []int
}

func newCacheMap32(maxBytes int64) *cacheMap32 {
	if maxBytes <= 0 {
		maxBytes = defaultMaxCacheMemory
	}

	hints, _ := sizehelper.CalcNumEntries(8, 32, maxBytes)

	cms := &cacheMap32{
		overflow: make(map[int64][32]byte),
	}
	if len(hints) == 0 {
		cms.maps = []map[int64][32]byte{make(map[int64][32]byte, 1)}
		cms.maxEntries = []int{1}
		return cms
	}
	for _, hint := range hints {
		cms.maps = append(cms.maps, make(map[int64][32]byte, hint))
		cms.maxEntries = append(cms.maxEntries, hint)
	}
	return cms
}

func (cms *cacheMap32) entrySize() int { return 32 }

func (cms *cacheMap32) get(offset int64) ([]byte, bool) {
	for _, m := range cms.maps {
		if data, ok := m[offset]; ok {
			return data[:], true
		}
	}
	if data, ok := cms.overflow[offset]; ok {
		return data[:], true
	}
	return nil, false
}

func (cms *cacheMap32) put32(offset int64, data [32]byte) {
	for _, m := range cms.maps {
		if _, ok := m[offset]; ok {
			m[offset] = data
			return
		}
	}
	if _, ok := cms.overflow[offset]; ok {
		cms.overflow[offset] = data
		return
	}
	for i, m := range cms.maps {
		if len(m) < cms.maxEntries[i] {
			m[offset] = data
			return
		}
	}
	cms.overflow[offset] = data
}

func (cms *cacheMap32) delete(offset int64) {
	for _, m := range cms.maps {
		if _, ok := m[offset]; ok {
			delete(m, offset)
			return
		}
	}
	delete(cms.overflow, offset)
}

func (cms *cacheMap32) deleteAbove(size int64) {
	for _, m := range cms.maps {
		for offset := range m {
			if offset >= size {
				delete(m, offset)
			}
		}
	}
	for offset := range cms.overflow {
		if offset >= size {
			delete(cms.overflow, offset)
		}
	}
}

func (cms *cacheMap32) clear() {
	for _, m := range cms.maps {
		clear(m)
	}
	clear(cms.overflow)
}

func (cms *cacheMap32) forEach(fn func(offset int64, data []byte)) {
	for _, m := range cms.maps {
		for offset, data := range m {
			fn(offset, data[:])
		}
	}
	for offset, data := range cms.overflow {
		fn(offset, data[:])
	}
}

func (cms *cacheMap32) overflowed() bool { return len(cms.overflow) > 0 }

func (cms *cacheMap32) count() int {
	total := len(cms.overflow)
	for _, m := range cms.maps {
		total += len(m)
	}
	return total
}

// cacheMapBudget returns the largest map hint whose allocation fits within
// maxBytes for a map with the given key and value sizes.
func cacheMapBudget(maxBytes int64, keySize, valueSize int) int {
	hint := sizehelper.HintForMapMemory(int(maxBytes), keySize, valueSize)
	// HintForMapMemory returns the smallest hint that allocates >= maxBytes.
	// We want the largest hint that fits within maxBytes.
	if hint > 0 && int64(sizehelper.MapMemory(hint, keySize, valueSize)) > maxBytes {
		hint--
	}
	if hint < 1 {
		hint = 1
	}
	return hint
}

// cacheMap8 stores 8-byte entries (uint64 positions) in a single Go map.
type cacheMap8 struct {
	m      map[int64][8]byte
	budget int
}

func newCacheMap8(maxBytes int64) *cacheMap8 {
	if maxBytes <= 0 {
		maxBytes = defaultMaxCacheMemory
	}
	budget := cacheMapBudget(maxBytes, 8, 8)
	return &cacheMap8{
		m:      make(map[int64][8]byte, budget),
		budget: budget,
	}
}

func (cms *cacheMap8) entrySize() int { return 8 }

func (cms *cacheMap8) get(offset int64) ([]byte, bool) {
	if data, ok := cms.m[offset]; ok {
		return data[:], true
	}
	return nil, false
}

func (cms *cacheMap8) put8(offset int64, data [8]byte) {
	cms.m[offset] = data
}

func (cms *cacheMap8) delete(offset int64) {
	delete(cms.m, offset)
}

func (cms *cacheMap8) deleteAbove(size int64) {
	for offset := range cms.m {
		if offset >= size {
			delete(cms.m, offset)
		}
	}
}

func (cms *cacheMap8) clear() {
	clear(cms.m)
}

func (cms *cacheMap8) forEach(fn func(offset int64, data []byte)) {
	for offset, data := range cms.m {
		fn(offset, data[:])
	}
}

func (cms *cacheMap8) overflowed() bool { return len(cms.m) > cms.budget }

func (cms *cacheMap8) count() int { return len(cms.m) }

// cacheMap4 stores 4-byte entries (int32 addIndex) in a single Go map.
type cacheMap4 struct {
	m      map[int64][4]byte
	budget int
}

func newCacheMap4(maxBytes int64) *cacheMap4 {
	if maxBytes <= 0 {
		maxBytes = defaultMaxCacheMemory
	}
	budget := cacheMapBudget(maxBytes, 8, 4)
	return &cacheMap4{
		m:      make(map[int64][4]byte, budget),
		budget: budget,
	}
}

func (cms *cacheMap4) entrySize() int { return 4 }

func (cms *cacheMap4) get(offset int64) ([]byte, bool) {
	if data, ok := cms.m[offset]; ok {
		return data[:], true
	}
	return nil, false
}

func (cms *cacheMap4) put4(offset int64, data [4]byte) {
	cms.m[offset] = data
}

func (cms *cacheMap4) delete(offset int64) {
	delete(cms.m, offset)
}

func (cms *cacheMap4) deleteAbove(size int64) {
	for offset := range cms.m {
		if offset >= size {
			delete(cms.m, offset)
		}
	}
}

func (cms *cacheMap4) clear() {
	clear(cms.m)
}

func (cms *cacheMap4) forEach(fn func(offset int64, data []byte)) {
	for offset, data := range cms.m {
		fn(offset, data[:])
	}
}

func (cms *cacheMap4) overflowed() bool { return len(cms.m) > cms.budget }

func (cms *cacheMap4) count() int { return len(cms.m) }
