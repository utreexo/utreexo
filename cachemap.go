package utreexo

import "github.com/utreexo/utreexo/internal/sizehelper"

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

func (cms *cacheMap32) put(offset int64, data []byte) {
	cms.put32(offset, [32]byte(data))
}

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

// cacheMap8 stores 8-byte entries (uint64 positions).
type cacheMap8 struct {
	maps       []map[int64][8]byte
	overflow   map[int64][8]byte
	maxEntries []int
}

func newCacheMap8(maxBytes int64) *cacheMap8 {
	if maxBytes <= 0 {
		maxBytes = defaultMaxCacheMemory
	}

	hints, _ := sizehelper.CalcNumEntries(8, 8, maxBytes)

	cms := &cacheMap8{
		overflow: make(map[int64][8]byte),
	}
	if len(hints) == 0 {
		cms.maps = []map[int64][8]byte{make(map[int64][8]byte, 1)}
		cms.maxEntries = []int{1}
		return cms
	}
	for _, hint := range hints {
		cms.maps = append(cms.maps, make(map[int64][8]byte, hint))
		cms.maxEntries = append(cms.maxEntries, hint)
	}
	return cms
}

func (cms *cacheMap8) entrySize() int { return 8 }

func (cms *cacheMap8) put(offset int64, data []byte) {
	cms.put8(offset, [8]byte(data))
}

func (cms *cacheMap8) get(offset int64) ([]byte, bool) {
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

func (cms *cacheMap8) put8(offset int64, data [8]byte) {
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

func (cms *cacheMap8) delete(offset int64) {
	for _, m := range cms.maps {
		if _, ok := m[offset]; ok {
			delete(m, offset)
			return
		}
	}
	delete(cms.overflow, offset)
}

func (cms *cacheMap8) deleteAbove(size int64) {
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

func (cms *cacheMap8) clear() {
	for _, m := range cms.maps {
		clear(m)
	}
	clear(cms.overflow)
}

func (cms *cacheMap8) forEach(fn func(offset int64, data []byte)) {
	for _, m := range cms.maps {
		for offset, data := range m {
			fn(offset, data[:])
		}
	}
	for offset, data := range cms.overflow {
		fn(offset, data[:])
	}
}

func (cms *cacheMap8) overflowed() bool { return len(cms.overflow) > 0 }

func (cms *cacheMap8) count() int {
	total := len(cms.overflow)
	for _, m := range cms.maps {
		total += len(m)
	}
	return total
}

// cacheMap4 stores 4-byte entries (int32 addIndex).
type cacheMap4 struct {
	maps       []map[int64][4]byte
	overflow   map[int64][4]byte
	maxEntries []int
}

func newCacheMap4(maxBytes int64) *cacheMap4 {
	if maxBytes <= 0 {
		maxBytes = defaultMaxCacheMemory
	}

	hints, _ := sizehelper.CalcNumEntries(8, 4, maxBytes)

	cms := &cacheMap4{
		overflow: make(map[int64][4]byte),
	}
	if len(hints) == 0 {
		cms.maps = []map[int64][4]byte{make(map[int64][4]byte, 1)}
		cms.maxEntries = []int{1}
		return cms
	}
	for _, hint := range hints {
		cms.maps = append(cms.maps, make(map[int64][4]byte, hint))
		cms.maxEntries = append(cms.maxEntries, hint)
	}
	return cms
}

func (cms *cacheMap4) entrySize() int { return 4 }

func (cms *cacheMap4) put(offset int64, data []byte) {
	cms.put4(offset, [4]byte(data))
}

func (cms *cacheMap4) get(offset int64) ([]byte, bool) {
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

func (cms *cacheMap4) put4(offset int64, data [4]byte) {
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

func (cms *cacheMap4) delete(offset int64) {
	for _, m := range cms.maps {
		if _, ok := m[offset]; ok {
			delete(m, offset)
			return
		}
	}
	delete(cms.overflow, offset)
}

func (cms *cacheMap4) deleteAbove(size int64) {
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

func (cms *cacheMap4) clear() {
	for _, m := range cms.maps {
		clear(m)
	}
	clear(cms.overflow)
}

func (cms *cacheMap4) forEach(fn func(offset int64, data []byte)) {
	for _, m := range cms.maps {
		for offset, data := range m {
			fn(offset, data[:])
		}
	}
	for offset, data := range cms.overflow {
		fn(offset, data[:])
	}
}

func (cms *cacheMap4) overflowed() bool { return len(cms.overflow) > 0 }

func (cms *cacheMap4) count() int {
	total := len(cms.overflow)
	for _, m := range cms.maps {
		total += len(m)
	}
	return total
}
