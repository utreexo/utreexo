package utreexo

import (
	"fmt"
	"io"
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

	// delete removes the entry at the given offset.
	delete(offset int64)

	// deleteAbove removes all entries at offsets >= size (used for truncation).
	deleteAbove(size int64)

	// clear removes all entries from the cache.
	clear()

	// clearDirty resets dirty tracking but keeps all entries cached.
	// After clearDirty, forEach iterates nothing and subsequent puts to
	// existing entries take the fast path.
	clearDirty()

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

// cachedRWS wraps an io.ReadWriteSeeker, buffering all writes in memory.
// Reads check the buffer first (exact offset match), then fall through to
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
	cache      cacheStore
	pos        int64 // current seek position
	maxWritten int64 // highest byte offset written (for SeekEnd)
	baseSize   int64 // underlying file size at wrap time
}

// newCachedRWS creates a cachedRWS wrapping the given io.ReadWriteSeeker.
// It seeks to the end of the underlying file to determine its current size,
// which is needed for correct SeekEnd behavior (e.g. append patterns).
// entrySize specifies the fixed record size (4, 8, or 32 bytes).
// maxCacheBytes controls when overflowed() signals that a flush is needed.
// If maxCacheBytes is 0, defaultMaxCacheMemory is used.
func newCachedRWS(underlying forestFile, entrySize int, maxCacheBytes int64) (*cachedRWS, error) {
	size, err := underlying.Seek(0, io.SeekEnd)
	if err != nil {
		return nil, err
	}
	if maxCacheBytes <= 0 {
		maxCacheBytes = defaultMaxCacheMemory
	}

	cache, err := newMmapCacheStore(entrySize, maxCacheBytes)
	if err != nil {
		return nil, err
	}

	return &cachedRWS{
		underlying: underlying,
		cache:      cache,
		pos:        size,
		maxWritten: size,
		baseSize:   size,
	}, nil
}

// WriteAt writes len(p) bytes starting at byte offset off.
// The data is stored in the cache (same as Write) without touching the
// underlying file. Unlike Write, it does not advance the seek position,
// making it safe for concurrent use when callers write to disjoint offsets.
//
// p may be a single entry or a contiguous batch of entries (len must be
// a multiple of entrySize). Each entry is stored as a separate cache put.
func (c *cachedRWS) WriteAt(p []byte, off int64) (int, error) {
	es := c.cache.entrySize()
	if len(p)%es != 0 {
		return 0, fmt.Errorf("expected multiple of %d bytes, got %d", es, len(p))
	}
	for i := 0; i < len(p); i += es {
		if err := c.cache.put(off+int64(i), p[i:i+es]); err != nil {
			return i, err
		}
	}
	end := off + int64(len(p))
	if end > c.maxWritten {
		c.maxWritten = end
	}
	return len(p), nil
}

// ReadAt reads len(p) bytes starting at byte offset off.
// It checks the cache first, then falls through to the underlying file.
func (c *cachedRWS) ReadAt(p []byte, off int64) (int, error) {
	if cached, ok := c.cache.get(off); ok {
		n := copy(p, cached)
		if n < len(p) {
			return n, io.EOF
		}
		return n, nil
	}
	if off >= c.baseSize {
		return 0, io.EOF
	}
	return c.underlying.ReadAt(p, off)
}

// Read returns data from the cache if present, otherwise reads from
// the underlying file. Positions beyond the underlying file size
// return zeros without touching the file.
func (c *cachedRWS) Read(p []byte) (int, error) {
	if cached, ok := c.cache.get(c.pos); ok {
		n := copy(p, cached)
		c.pos += int64(n)
		return n, nil
	}
	// If the read is entirely beyond the underlying file, return zeros
	// without touching it. This avoids extending an in-memory file (or
	// hitting EOF on a real file) for positions that only exist in the cache.
	if c.pos >= c.baseSize {
		for i := range p {
			p[i] = 0
		}
		n := len(p)
		c.pos += int64(n)
		return n, nil
	}
	// Fall through to underlying file.
	_, err := c.underlying.Seek(c.pos, io.SeekStart)
	if err != nil {
		return 0, err
	}
	n, err := c.underlying.Read(p)
	c.pos += int64(n)
	return n, err
}

// Write stores data in the cache at the current position. The data length
// must match the cache's entry size (4, 8, or 32 bytes).
func (c *cachedRWS) Write(p []byte) (int, error) {
	if len(p) != c.cache.entrySize() {
		return 0, fmt.Errorf("expected %d bytes, got %d", c.cache.entrySize(), len(p))
	}
	if err := c.cache.put(c.pos, p); err != nil {
		return 0, err
	}

	n := len(p)
	c.pos += int64(n)
	if c.pos > c.maxWritten {
		c.maxWritten = c.pos
	}
	return n, nil
}

// Seek sets the position for the next Read or Write. For SeekEnd,
// the end is defined as maxWritten (the highest position written to).
func (c *cachedRWS) Seek(offset int64, whence int) (int64, error) {
	switch whence {
	case io.SeekStart:
		c.pos = offset
	case io.SeekCurrent:
		c.pos += offset
	case io.SeekEnd:
		c.pos = c.maxWritten + offset
	default:
		return 0, fmt.Errorf("cachedRWS: invalid whence %d", whence)
	}
	return c.pos, nil
}

// Flush writes all cached data to the underlying file and clears the cache.
func (c *cachedRWS) Flush() error {
	var flushErr error
	c.cache.forEach(func(offset int64, data []byte) {
		if flushErr != nil {
			return
		}
		_, err := c.underlying.Seek(offset, io.SeekStart)
		if err != nil {
			flushErr = err
			return
		}
		_, err = c.underlying.Write(data)
		if err != nil {
			flushErr = err
			return
		}
	})
	if flushErr != nil {
		return flushErr
	}
	// Keep entries cached (bitmap + data intact) but reset dirty tracking.
	// Subsequent writes to existing positions take the lock-free overwrite
	// fast path instead of contending on the dirty list lock.
	c.cache.clearDirty()

	// Update baseSize so subsequent reads can reach the newly flushed data
	// in the underlying file.
	size, err := c.underlying.Seek(0, io.SeekEnd)
	if err != nil {
		return err
	}
	c.baseSize = size
	return nil
}

// Discard drops all buffered writes without touching the underlying file.
func (c *cachedRWS) Discard() {
	c.cache.clear()
	c.maxWritten = c.baseSize
	c.pos = 0
}

// Close releases resources held by the cache (e.g. mmap regions).
func (c *cachedRWS) Close() {
	c.cache.close()
}

// FlushNeeded returns true if the cache has exceeded its memory threshold.
func (c *cachedRWS) FlushNeeded() bool {
	return c.cache.overflowed()
}

// resetAfterFlush clears dirty tracking and updates baseSize/maxWritten to
// reflect the current underlying file size. This should be called after
// writes have been applied to the underlying file (e.g. by the WAL),
// so that a subsequent Discard resets to the correct post-flush baseline.
// Entries remain cached for fast overwrite paths.
func (c *cachedRWS) resetAfterFlush() error {
	c.cache.clearDirty()
	size, err := c.underlying.Seek(0, io.SeekEnd)
	if err != nil {
		return err
	}
	c.baseSize = size
	c.maxWritten = size
	c.pos = 0
	return nil
}

// Truncate truncates the underlying file to the specified size.
// It also invalidates any cached writes beyond the new size and updates
// the internal size tracking.
func (c *cachedRWS) Truncate(size int64) error {
	truncater, ok := c.underlying.(interface{ Truncate(int64) error })
	if !ok {
		return fmt.Errorf("underlying file does not support Truncate")
	}
	if err := truncater.Truncate(size); err != nil {
		return err
	}

	// Invalidate cached writes beyond the new size.
	c.cache.deleteAbove(size)

	// Update size tracking.
	c.baseSize = size
	if c.maxWritten > size {
		c.maxWritten = size
	}
	if c.pos > size {
		c.pos = size
	}

	return nil
}
