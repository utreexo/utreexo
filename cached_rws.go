package utreexo

import (
	"encoding/binary"
	"fmt"
	"io"
	"sync"
	"sync/atomic"
)

const (
	// defaultMaxCacheMemory is 64MB per cachedRWS.
	defaultMaxCacheMemory = 64 << 20
)

// cacheStore is the interface for underlying cache storage.
type cacheStore interface {
	// get retrieves the data at the given offset. Returns false if not found.
	// The returned slice aliases internal storage and must not be retained
	// or modified by the caller.
	get(offset int64) ([]byte, bool)

	// put stores data at the given offset. len(data) must equal entrySize().
	put(offset int64, data []byte) error

	// clear removes all entries from the cache.
	clear()

	// forEach iterates over all cached entries, calling fn for each.
	forEach(fn func(offset int64, data []byte))

	// overflowed returns true if the cache has exceeded its memory budget.
	overflowed() bool

	// count returns the total number of cached entries.
	count() int

	// entrySize returns the fixed size of each entry in bytes.
	entrySize() int

	// close releases any resources held by the cache (e.g. mmap regions).
	close()
}

// cachedRWS wraps a forestFile, buffering all writes in memory. Reads
// check the buffer first (exact offset match), then fall through to
// the underlying file on miss. This enables atomic modifications: call
// Flush to commit buffered writes, or Discard to throw them away.
//
// cachedRWS assumes all I/O is aligned, fixed-size records. Reads and
// writes at offset X always use the same record size. Partial overlap
// between a cached write and a subsequent read at a different offset is
// NOT handled -- the read will miss the cache and return stale data from
// the underlying file.
type cachedRWS struct {
	underlying forestFile
	// cache is the concrete production cache type (build-tagged alias).
	// Concrete dispatch lets escape analysis see through cache.put so
	// callers like PutHashAt can pass [32]byte by value without forcing
	// the local to heap.
	cache *cacheImpl
	// mu guards the in-memory cache map so the record and generate pipeline
	// stages can read and write disjoint file offsets concurrently. It is held
	// only around the map op, not around the underlying-file read on a miss, so
	// concurrent reads still overlap. maxWritten is atomic and baseSize is only
	// rewritten at flush time (when no pipeline stage runs), so neither needs mu.
	mu         sync.Mutex
	maxWritten atomic.Int64 // highest byte offset ever written (logical file size)
	baseSize   int64        // underlying file size at last flush
}

// newCachedRWS creates a cachedRWS wrapping the given forestFile.
// initialSize is the underlying file's current byte size; the caller is
// expected to know it (e.g. via Stat for *os.File or the size passed to
// mmapfile.Open). entrySize specifies the fixed record size (4, 8, or 32
// bytes). maxCacheBytes controls when overflowed() signals that a flush
// is needed; if 0, defaultMaxCacheMemory is used.
func newCachedRWS(underlying forestFile, entrySize int, maxCacheBytes, initialSize int64) (*cachedRWS, error) {
	if maxCacheBytes <= 0 {
		maxCacheBytes = defaultMaxCacheMemory
	}

	cache, err := newMmapCacheStore(entrySize, maxCacheBytes)
	if err != nil {
		return nil, err
	}

	c := &cachedRWS{
		underlying: underlying,
		cache:      cache,
		baseSize:   initialSize,
	}
	c.maxWritten.Store(initialSize)
	return c, nil
}

// Size returns the cachedRWS's current logical size, including any cached
// writes that haven't been flushed to the underlying file yet.
func (c *cachedRWS) Size() int64 {
	return c.maxWritten.Load()
}

// ReadAt reads len(p) bytes starting at byte offset off, checking the cache
// first and falling through to the underlying file on miss. Follows the
// io.ReaderAt contract: short reads return (n, io.EOF), and reads entirely
// past the underlying file size return (0, io.EOF). Callers that want
// "unwritten position reads as zero" semantics must handle io.EOF themselves.
func (c *cachedRWS) ReadAt(p []byte, off int64) (int, error) {
	c.mu.Lock()
	if cached, ok := c.cache.get(off); ok {
		n := copy(p, cached)
		c.mu.Unlock()
		if n < len(p) {
			return n, io.EOF
		}
		return n, nil
	}
	c.mu.Unlock()
	if off >= c.baseSize {
		return 0, io.EOF
	}
	return c.underlying.ReadAt(p, off)
}

// HashAt returns the 32 bytes at off as a [32]byte value, checking the cache
// first and falling through to the underlying file on miss. Returning by
// value lets callers verify hashes without allocating a buffer that would
// otherwise escape through io.ReaderAt.
func (c *cachedRWS) HashAt(off int64) ([32]byte, error) {
	c.mu.Lock()
	if cached, ok := c.cache.get(off); ok {
		var h [32]byte
		copy(h[:], cached)
		c.mu.Unlock()
		return h, nil
	}
	c.mu.Unlock()
	if off >= c.baseSize {
		return [32]byte{}, io.EOF
	}
	return c.underlying.HashAt(off)
}

// WriteAt writes p to the cache at byte offset off. The data length must
// match the cache's entry size. Safe for concurrent disjoint-offset
// writes from multiple goroutines (no shared seek position).
func (c *cachedRWS) WriteAt(p []byte, off int64) (int, error) {
	if len(p) != c.cache.entrySize() {
		return 0, fmt.Errorf("expected %d bytes, got %d", c.cache.entrySize(), len(p))
	}
	c.mu.Lock()
	err := c.cache.put(off, p)
	c.mu.Unlock()
	if err != nil {
		return 0, err
	}
	c.bumpMaxWritten(off + int64(len(p)))
	return len(p), nil
}

// PutHashAt is the value-taking 32-byte WriteAt. Callers pass the hash by
// value so the local-array-escapes-through-interface heap alloc that the
// []byte form causes can be avoided at the call site.
func (c *cachedRWS) PutHashAt(hash [32]byte, off int64) error {
	if c.cache.entrySize() != 32 {
		return fmt.Errorf("PutHashAt: entrySize %d != 32", c.cache.entrySize())
	}
	c.mu.Lock()
	err := c.cache.put(off, hash[:])
	c.mu.Unlock()
	if err != nil {
		return err
	}
	c.bumpMaxWritten(off + 32)
	return nil
}

// PutUint32At is the value-taking 4-byte WriteAt. Same motivation as PutHashAt.
func (c *cachedRWS) PutUint32At(val uint32, off int64) error {
	if c.cache.entrySize() != 4 {
		return fmt.Errorf("PutUint32At: entrySize %d != 4", c.cache.entrySize())
	}
	var buf [4]byte
	binary.LittleEndian.PutUint32(buf[:], val)
	c.mu.Lock()
	err := c.cache.put(off, buf[:])
	c.mu.Unlock()
	if err != nil {
		return err
	}
	c.bumpMaxWritten(off + 4)
	return nil
}

func (c *cachedRWS) bumpMaxWritten(end int64) {
	for {
		old := c.maxWritten.Load()
		if end <= old {
			return
		}
		if c.maxWritten.CompareAndSwap(old, end) {
			return
		}
	}
}

// Flush writes all cached data to the underlying file and clears the cache.
func (c *cachedRWS) Flush() error {
	c.mu.Lock()
	defer c.mu.Unlock()
	var flushErr error
	c.cache.forEach(func(offset int64, data []byte) {
		if flushErr != nil {
			return
		}
		if _, err := c.underlying.WriteAt(data, offset); err != nil {
			flushErr = err
			return
		}
	})
	if flushErr != nil {
		return flushErr
	}
	c.cache.clear()

	// All cached writes have been applied to the underlying file, so the
	// underlying's new size is exactly maxWritten.
	c.baseSize = c.maxWritten.Load()
	return nil
}

// Discard drops all buffered writes without touching the underlying file.
func (c *cachedRWS) Discard() {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.cache.clear()
	c.maxWritten.Store(c.baseSize)
}

// Close releases resources held by the cache (e.g. mmap regions).
func (c *cachedRWS) Close() {
	c.cache.close()
}

// FlushNeeded returns true if the cache has exceeded its memory threshold.
func (c *cachedRWS) FlushNeeded() bool {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.cache.overflowed()
}

// Truncate shrinks the underlying file to size and updates cachedRWS's
// own size tracking. Used by reconciliation logic at open time to trim
// stale tail data (e.g. block-count entries left behind by an unflushed
// undo before a crash). The underlying must satisfy Truncate; rawFile
// (wrapping *os.File) and memFile do, mmapFile does not.
//
// maxWritten is clamped via CAS rather than a plain Store so this stays
// safe if a future caller races it against WriteAt -- the inverse of
// bumpMaxWritten, lowering instead of raising.
func (c *cachedRWS) Truncate(size int64) error {
	t, ok := c.underlying.(interface{ Truncate(int64) error })
	if !ok {
		return fmt.Errorf("cachedRWS: underlying does not support Truncate")
	}
	if err := t.Truncate(size); err != nil {
		return err
	}
	if size < c.baseSize {
		c.baseSize = size
	}
	for {
		old := c.maxWritten.Load()
		if size >= old {
			break
		}
		if c.maxWritten.CompareAndSwap(old, size) {
			break
		}
	}
	return nil
}

// resetAfterFlush clears the cache and updates baseSize to reflect the
// current underlying file size. This should be called after writes have
// been applied to the underlying file (e.g. by the WAL), so that a
// subsequent Discard resets to the correct post-flush baseline.
func (c *cachedRWS) resetAfterFlush() error {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.cache.clear()
	c.baseSize = c.maxWritten.Load()
	return nil
}
