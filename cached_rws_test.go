package utreexo

import (
	"encoding/binary"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestCachedRWSReadWrite(t *testing.T) {
	underlying := newMemFile()

	// Pre-populate underlying with 32 bytes at offset 0.
	hash := testHashFromInt(1)
	_, err := underlying.WriteAt(hash[:], 0)
	require.NoError(t, err)

	c, err := newCachedRWS(underlying, 32, 0, underlying.Size())
	require.NoError(t, err)

	// Read from underlying (cache miss).
	var got [32]byte
	n, err := c.ReadAt(got[:], 0)
	require.NoError(t, err)
	require.Equal(t, 32, n)
	require.Equal(t, hash, Hash(got))

	// Write a new hash at offset 0 (only goes to cache).
	newHash := testHashFromInt(2)
	n, err = c.WriteAt(newHash[:], 0)
	require.NoError(t, err)
	require.Equal(t, 32, n)

	// Read back from cache (should see new hash, not underlying).
	n, err = c.ReadAt(got[:], 0)
	require.NoError(t, err)
	require.Equal(t, 32, n)
	require.Equal(t, newHash, Hash(got))

	// Underlying should still have the original hash.
	n, err = underlying.ReadAt(got[:], 0)
	require.NoError(t, err)
	require.Equal(t, 32, n)
	require.Equal(t, hash, Hash(got))
}

func TestCachedRWSAppend(t *testing.T) {
	// Simulate the deletedFile append pattern: WriteAt at the current
	// Size(), repeated.
	underlying := newMemFile()

	// Write an 8-byte header to underlying.
	var header [8]byte
	_, err := underlying.WriteAt(header[:], 0)
	require.NoError(t, err)

	c, err := newCachedRWS(underlying, 8, 0, underlying.Size())
	require.NoError(t, err)

	// Append three 8-byte entries.
	for i := uint64(0); i < 3; i++ {
		off := c.Size()
		require.Equal(t, int64(8+i*8), off, "append %d should be at correct offset", i)

		var buf [8]byte
		binary.LittleEndian.PutUint64(buf[:], i+100)
		_, err = c.WriteAt(buf[:], off)
		require.NoError(t, err)
	}

	// Read them back from cache.
	for i := uint64(0); i < 3; i++ {
		var buf [8]byte
		_, err = c.ReadAt(buf[:], int64(8+i*8))
		require.NoError(t, err)
		require.Equal(t, i+100, binary.LittleEndian.Uint64(buf[:]))
	}
}

func TestCachedRWSFlush(t *testing.T) {
	underlying := newMemFile()

	c, err := newCachedRWS(underlying, 32, 0, underlying.Size())
	require.NoError(t, err)

	// Write two hashes at different offsets.
	h1 := testHashFromInt(10)
	h2 := testHashFromInt(20)

	_, err = c.WriteAt(h1[:], 0)
	require.NoError(t, err)
	_, err = c.WriteAt(h2[:], 32)
	require.NoError(t, err)

	// Underlying should be empty before flush.
	require.Equal(t, 0, len(underlying.data))

	// Flush.
	err = c.Flush()
	require.NoError(t, err)

	// Underlying should now have both hashes.
	require.Equal(t, 64, len(underlying.data))

	var got [32]byte
	_, err = underlying.ReadAt(got[:], 0)
	require.NoError(t, err)
	require.Equal(t, h1, Hash(got))

	_, err = underlying.ReadAt(got[:], 32)
	require.NoError(t, err)
	require.Equal(t, h2, Hash(got))

	// Cache should be empty after flush.
	require.Equal(t, 0, c.cache.count())
}

func TestCachedRWSDiscard(t *testing.T) {
	underlying := newMemFile()

	// Pre-populate underlying.
	origHash := testHashFromInt(42)
	_, err := underlying.WriteAt(origHash[:], 0)
	require.NoError(t, err)

	c, err := newCachedRWS(underlying, 32, 0, underlying.Size())
	require.NoError(t, err)

	// Write a different hash at offset 0.
	newHash := testHashFromInt(99)
	_, err = c.WriteAt(newHash[:], 0)
	require.NoError(t, err)

	// Also write beyond the original file.
	_, err = c.WriteAt(newHash[:], 32)
	require.NoError(t, err)

	// Discard.
	c.Discard()

	// Cache should be empty.
	require.Equal(t, 0, c.cache.count())

	// maxWritten should be reset to baseSize.
	require.Equal(t, c.baseSize, c.maxWritten)

	// Read from offset 0 should return the original hash (from underlying).
	var got [32]byte
	n, err := c.ReadAt(got[:], 0)
	require.NoError(t, err)
	require.Equal(t, 32, n)
	require.Equal(t, origHash, Hash(got))

	// Underlying data should be unchanged (only 32 bytes).
	require.Equal(t, 32, len(underlying.data))
}

func TestCachedRWSReadAfterWrite(t *testing.T) {
	underlying := newMemFile()

	// Pre-populate with a stale hash.
	stale := testHashFromInt(1)
	_, err := underlying.WriteAt(stale[:], 0)
	require.NoError(t, err)

	c, err := newCachedRWS(underlying, 32, 0, underlying.Size())
	require.NoError(t, err)

	// Write a fresh hash at the same offset.
	fresh := testHashFromInt(2)
	_, err = c.WriteAt(fresh[:], 0)
	require.NoError(t, err)

	// Read at the same offset should return the fresh hash.
	var got [32]byte
	_, err = c.ReadAt(got[:], 0)
	require.NoError(t, err)
	require.Equal(t, fresh, Hash(got))
}

func TestCachedRWSConcurrentDisjointWrites(t *testing.T) {
	underlying := newMemFile()

	c, err := newCachedRWS(underlying, 32, 0, underlying.Size())
	require.NoError(t, err)

	const numWriters = 64
	hashes := make([]Hash, numWriters)
	for i := range hashes {
		hashes[i] = testHashFromInt(i + 1)
	}

	// Release all goroutines simultaneously to maximize overlap.
	// Each writer targets its own disjoint 32-byte slot and writes into
	// its own slot in errs, so the slice itself is race-free.
	start := make(chan struct{})
	errs := make([]error, numWriters)
	var wg sync.WaitGroup
	wg.Add(numWriters)
	for i := 0; i < numWriters; i++ {
		go func(i int) {
			defer wg.Done()
			<-start
			_, errs[i] = c.WriteAt(hashes[i][:], int64(i)*32)
		}(i)
	}
	close(start)
	wg.Wait()

	for i, err := range errs {
		require.NoErrorf(t, err, "writer %d", i)
	}

	// Every disjoint write should be readable from cache at its own offset.
	for i := 0; i < numWriters; i++ {
		var got [32]byte
		n, err := c.ReadAt(got[:], int64(i)*32)
		require.NoError(t, err)
		require.Equal(t, 32, n)
		require.Equalf(t, hashes[i], Hash(got), "offset %d", i*32)
	}

	require.Equal(t, int64(numWriters)*32, c.Size())
}
