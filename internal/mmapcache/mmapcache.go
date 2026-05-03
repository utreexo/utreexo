// Package mmapcache provides a cache backed by a single anonymous mmap region.
// The region covers the full data file address space but pages are
// demand-paged by the kernel, so only touched pages consume physical memory.
// A separate presence bitmap tracks which slots have cached data (for Get).
// A dirty bitmap tracks which slots were written since the last ClearDirty
// (for ForEach). Atomic range tracking [dirtyMinWord, dirtyMaxWord] bounds
// the ForEach scan without any mutex or dense list, making Put fully lock-free.
package mmapcache

import (
	"fmt"
	"math"
	"math/bits"
	"sync/atomic"
	"unsafe"
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
// Concurrency:
//   - Get and Put on disjoint slots may run concurrently without external
//     synchronization. Put is lock-free in this case (atomic CAS on bitmap
//     words plus atomic min/max updates for range tracking).
//   - Put on the same slot, or Get concurrent with a Put that overwrites
//     that same slot, races on the data region (the byte copy is not
//     atomic and is not fenced for re-writes). Callers must serialize
//     same-slot access externally.
//   - ForEach, Clear, ClearDirty, Delete, DeleteAbove, and Close are NOT
//     safe to call concurrently with any other method.
type Store struct {
	data        []byte // mmap'd data region (demand-paged)
	bitmap      []byte // mmap'd presence bitmap; tracks which slots have cached data for Get
	dirtyBitmap []byte // mmap'd dirty bitmap; tracks which slots were written since last ClearDirty

	entrySize  int
	slots      int // total number of slots
	words      int // number of uint64 words in each bitmap
	maxEntries int
	totalCount atomic.Int64

	// Atomic range of dirty bitmap word indices. ForEach scans only
	// [dirtyMinWord, dirtyMaxWord]. Initialized to empty (min > max).
	dirtyMinWord atomic.Int64
	dirtyMaxWord atomic.Int64

	// Atomic range of presence bitmap word indices. Clear and DeleteAbove
	// use this to find all present entries.
	presMinWord atomic.Int64
	presMaxWord atomic.Int64
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

	s := &Store{
		data:        data,
		bitmap:      bitmap,
		dirtyBitmap: dirtyBitmap,
		entrySize:   entrySize,
		slots:       slots,
		words:       words,
		maxEntries:  int(maxBytes) / entrySize,
	}
	// Initialize range sentinels to "empty".
	s.dirtyMinWord.Store(math.MaxInt64)
	s.dirtyMaxWord.Store(-1)
	s.presMinWord.Store(math.MaxInt64)
	s.presMaxWord.Store(-1)
	return s, nil
}

// EntrySize returns the fixed size of each entry in bytes.
func (s *Store) EntrySize() int { return s.entrySize }

// bmWordPtr returns an atomic pointer to the w-th uint64 in the given bitmap.
func bmWordPtr(bm []byte, w int) *uint64 {
	return (*uint64)(unsafe.Pointer(&bm[w*8]))
}

// atomicMinInt64 atomically updates *addr = min(*addr, val).
func atomicMinInt64(addr *atomic.Int64, val int64) {
	for {
		old := addr.Load()
		if val >= old {
			return
		}
		if addr.CompareAndSwap(old, val) {
			return
		}
	}
}

// atomicMaxInt64 atomically updates *addr = max(*addr, val).
func atomicMaxInt64(addr *atomic.Int64, val int64) {
	for {
		old := addr.Load()
		if val <= old {
			return
		}
		if addr.CompareAndSwap(old, val) {
			return
		}
	}
}

// Get retrieves the data at the given byte offset. Returns nil, false if
// the offset has no cached entry. The returned slice aliases internal storage.
//
// Lock-free: uses an atomic bitmap load. Safe to call concurrently with
// Put/Get on disjoint slots. Concurrent with a Put that overwrites this
// same slot, the returned bytes may be torn — see the Store doc.
func (s *Store) Get(offset int64) ([]byte, bool) {
	slot := int(offset) / s.entrySize
	w, bit := slot/bitsPerWord, uint(slot)%bitsPerWord

	if atomic.LoadUint64(bmWordPtr(s.bitmap, w))>>bit&1 == 0 {
		return nil, false
	}
	start := slot * s.entrySize
	return s.data[start : start+s.entrySize], true
}

// Put stores data at the given byte offset. len(data) must equal EntrySize().
//
// Lock-free with respect to other slots: uses atomic CAS on the presence and
// dirty bitmaps and atomic min/max updates for range tracking. Same-slot
// concurrency (two Puts, or a Put overwriting while another goroutine Gets)
// races on the data region and must be serialized externally — see the
// Store doc.
func (s *Store) Put(offset int64, data []byte) error {
	if len(data) != s.entrySize {
		return fmt.Errorf("mmapcache: Put: len(data)=%d, want %d", len(data), s.entrySize)
	}
	slot := int(offset) / s.entrySize
	start := slot * s.entrySize

	// Data copy to disjoint slot — safe without lock.
	copy(s.data[start:start+s.entrySize], data)

	w, bit := slot/bitsPerWord, uint(slot)%bitsPerWord
	mask := uint64(1) << bit
	wInt64 := int64(w)

	// Set presence bitmap bit (for Get cache hits).
	presPtr := bmWordPtr(s.bitmap, w)
	for {
		old := atomic.LoadUint64(presPtr)
		if old&mask != 0 {
			break // already present
		}
		if atomic.CompareAndSwapUint64(presPtr, old, old|mask) {
			atomicMinInt64(&s.presMinWord, wInt64)
			atomicMaxInt64(&s.presMaxWord, wInt64)
			break
		}
	}

	// Set dirty bitmap bit (for ForEach iteration).
	dirtyPtr := bmWordPtr(s.dirtyBitmap, w)
	for {
		old := atomic.LoadUint64(dirtyPtr)
		if old&mask != 0 {
			// Already dirty — nothing to do.
			return nil
		}
		if atomic.CompareAndSwapUint64(dirtyPtr, old, old|mask) {
			s.totalCount.Add(1)
			atomicMinInt64(&s.dirtyMinWord, wInt64)
			atomicMaxInt64(&s.dirtyMaxWord, wInt64)
			return nil
		}
	}
}

// Delete removes the entry at the given byte offset.
//
// NOT safe for concurrent use with ForEach, Clear, or Close.
func (s *Store) Delete(offset int64) {
	slot := int(offset) / s.entrySize
	w, bit := slot/bitsPerWord, uint(slot)%bitsPerWord
	mask := uint64(1) << bit

	// Clear presence bitmap.
	presPtr := bmWordPtr(s.bitmap, w)
	for {
		old := atomic.LoadUint64(presPtr)
		if old&mask == 0 {
			break
		}
		if atomic.CompareAndSwapUint64(presPtr, old, old&^mask) {
			break
		}
	}

	// Clear dirty bitmap and decrement count if it was dirty.
	dirtyPtr := bmWordPtr(s.dirtyBitmap, w)
	for {
		old := atomic.LoadUint64(dirtyPtr)
		if old&mask == 0 {
			return
		}
		if atomic.CompareAndSwapUint64(dirtyPtr, old, old&^mask) {
			s.totalCount.Add(-1)
			return
		}
	}
}

// DeleteAbove removes all entries at offsets >= size (used for truncation).
//
// NOT safe for concurrent use with Get/Put.
func (s *Store) DeleteAbove(size int64) {
	startSlot := int(size) / s.entrySize
	startWord := startSlot / bitsPerWord

	lo := int(s.presMinWord.Load())
	hi := int(s.presMaxWord.Load())
	if lo > hi {
		return
	}
	if startWord > lo {
		lo = startWord
	}

	for w := lo; w <= hi; w++ {
		var keepMask uint64
		if w == startWord {
			keepBits := uint(startSlot) % bitsPerWord
			keepMask = (1 << keepBits) - 1
		}
		// Clear presence bitmap.
		presWord := atomic.LoadUint64(bmWordPtr(s.bitmap, w))
		if presWord != 0 {
			atomic.StoreUint64(bmWordPtr(s.bitmap, w), presWord&keepMask)
		}
		// Clear dirty bitmap and adjust count.
		dirtyWord := atomic.LoadUint64(bmWordPtr(s.dirtyBitmap, w))
		if dirtyWord != 0 {
			cleared := bits.OnesCount64(dirtyWord) - bits.OnesCount64(dirtyWord&keepMask)
			atomic.StoreUint64(bmWordPtr(s.dirtyBitmap, w), dirtyWord&keepMask)
			s.totalCount.Add(int64(-cleared))
		}
	}
}

// Clear removes all entries. The mmap regions remain allocated so the
// store can be reused without re-mapping.
//
// NOT safe for concurrent use with Get/Put.
func (s *Store) Clear() {
	// Clear presence bitmap in its tracked range.
	lo := int(s.presMinWord.Load())
	hi := int(s.presMaxWord.Load())
	for w := lo; w <= hi; w++ {
		if atomic.LoadUint64(bmWordPtr(s.bitmap, w)) != 0 {
			atomic.StoreUint64(bmWordPtr(s.bitmap, w), 0)
		}
	}
	// Clear dirty bitmap in its tracked range.
	dlo := int(s.dirtyMinWord.Load())
	dhi := int(s.dirtyMaxWord.Load())
	for w := dlo; w <= dhi; w++ {
		if atomic.LoadUint64(bmWordPtr(s.dirtyBitmap, w)) != 0 {
			atomic.StoreUint64(bmWordPtr(s.dirtyBitmap, w), 0)
		}
	}
	s.totalCount.Store(0)
	s.dirtyMinWord.Store(math.MaxInt64)
	s.dirtyMaxWord.Store(-1)
	s.presMinWord.Store(math.MaxInt64)
	s.presMaxWord.Store(-1)
}

// ClearDirty resets the dirty tracking but keeps all cached entries
// readable (presence bitmap and data are preserved). The dirty bitmap
// is cleared so ForEach iterates nothing. Subsequent Puts to positions
// that are already present will need one CAS on the dirty bitmap, but
// after that repeated writes to the same position are fully lock-free.
//
// NOT safe for concurrent use with Get/Put.
func (s *Store) ClearDirty() {
	lo := int(s.dirtyMinWord.Load())
	hi := int(s.dirtyMaxWord.Load())
	for w := lo; w <= hi; w++ {
		if atomic.LoadUint64(bmWordPtr(s.dirtyBitmap, w)) != 0 {
			atomic.StoreUint64(bmWordPtr(s.dirtyBitmap, w), 0)
		}
	}
	s.totalCount.Store(0)
	s.dirtyMinWord.Store(math.MaxInt64)
	s.dirtyMaxWord.Store(-1)
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
	s.totalCount.Store(0)
}

// ForEach iterates over all dirty entries (written since last ClearDirty),
// calling fn for each one. Uses atomic range tracking to bound the scan.
//
// NOT safe for concurrent use with Put/Delete.
func (s *Store) ForEach(fn func(offset int64, data []byte)) {
	lo := int(s.dirtyMinWord.Load())
	hi := int(s.dirtyMaxWord.Load())
	for w := lo; w <= hi; w++ {
		word := atomic.LoadUint64(bmWordPtr(s.dirtyBitmap, w))
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
func (s *Store) Overflowed() bool { return int(s.totalCount.Load()) > s.maxEntries }

// Count returns the total number of dirty entries.
func (s *Store) Count() int { return int(s.totalCount.Load()) }
