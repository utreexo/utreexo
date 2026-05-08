package utreexo

import (
	"encoding/binary"
	"io"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestCachedRWSReadWrite(t *testing.T) {
	underlying := newMemFile()

	// Pre-populate underlying with 32 bytes at offset 0.
	hash := testHashFromInt(1)
	_, err := underlying.Write(hash[:])
	require.NoError(t, err)

	c, err := newCachedRWS(underlying, 32, 0, underlying.Size())
	require.NoError(t, err)

	// Read from underlying (cache miss).
	_, err = c.Seek(0, io.SeekStart)
	require.NoError(t, err)
	var got [32]byte
	n, err := c.Read(got[:])
	require.NoError(t, err)
	require.Equal(t, 32, n)
	require.Equal(t, hash, Hash(got))

	// Write a new hash at offset 0 (only goes to cache).
	newHash := testHashFromInt(2)
	_, err = c.Seek(0, io.SeekStart)
	require.NoError(t, err)
	n, err = c.Write(newHash[:])
	require.NoError(t, err)
	require.Equal(t, 32, n)

	// Read back from cache (should see new hash, not underlying).
	_, err = c.Seek(0, io.SeekStart)
	require.NoError(t, err)
	n, err = c.Read(got[:])
	require.NoError(t, err)
	require.Equal(t, 32, n)
	require.Equal(t, newHash, Hash(got))

	// Underlying should still have the original hash.
	_, err = underlying.Seek(0, io.SeekStart)
	require.NoError(t, err)
	n, err = underlying.Read(got[:])
	require.NoError(t, err)
	require.Equal(t, 32, n)
	require.Equal(t, hash, Hash(got))
}

func TestCachedRWSSeekEndAppend(t *testing.T) {
	// Simulate the deletedFile append pattern:
	// Seek(0, SeekEnd) then Write(8 bytes), repeated.
	underlying := newMemFile()

	// Write an 8-byte header to underlying.
	var header [8]byte
	_, err := underlying.Write(header[:])
	require.NoError(t, err)

	c, err := newCachedRWS(underlying, 8, 0, underlying.Size())
	require.NoError(t, err)

	// Append three 8-byte entries via SeekEnd.
	for i := uint64(0); i < 3; i++ {
		pos, err := c.Seek(0, io.SeekEnd)
		require.NoError(t, err)
		require.Equal(t, int64(8+i*8), pos, "append %d should be at correct offset", i)

		err = binary.Write(c, binary.LittleEndian, i+100)
		require.NoError(t, err)
	}

	// Read them back from cache.
	for i := uint64(0); i < 3; i++ {
		_, err = c.Seek(int64(8+i*8), io.SeekStart)
		require.NoError(t, err)
		var val uint64
		err = binary.Read(c, binary.LittleEndian, &val)
		require.NoError(t, err)
		require.Equal(t, i+100, val)
	}
}

func TestCachedRWSFlush(t *testing.T) {
	underlying := newMemFile()

	c, err := newCachedRWS(underlying, 32, 0, underlying.Size())
	require.NoError(t, err)

	// Write two hashes at different offsets.
	h1 := testHashFromInt(10)
	h2 := testHashFromInt(20)

	_, err = c.Seek(0, io.SeekStart)
	require.NoError(t, err)
	_, err = c.Write(h1[:])
	require.NoError(t, err)
	_, err = c.Seek(32, io.SeekStart)
	require.NoError(t, err)
	_, err = c.Write(h2[:])
	require.NoError(t, err)

	// Underlying should be empty before flush.
	require.Equal(t, 0, len(underlying.data))

	// Flush.
	err = c.Flush()
	require.NoError(t, err)

	// Underlying should now have both hashes.
	require.Equal(t, 64, len(underlying.data))

	var got [32]byte
	_, err = underlying.Seek(0, io.SeekStart)
	require.NoError(t, err)
	_, err = underlying.Read(got[:])
	require.NoError(t, err)
	require.Equal(t, h1, Hash(got))

	_, err = underlying.Read(got[:])
	require.NoError(t, err)
	require.Equal(t, h2, Hash(got))

	// Cache should be empty after flush.
	require.Equal(t, 0, c.cache.count())
}

func TestCachedRWSDiscard(t *testing.T) {
	underlying := newMemFile()

	// Pre-populate underlying.
	origHash := testHashFromInt(42)
	_, err := underlying.Write(origHash[:])
	require.NoError(t, err)

	c, err := newCachedRWS(underlying, 32, 0, underlying.Size())
	require.NoError(t, err)

	// Write a different hash at offset 0.
	newHash := testHashFromInt(99)
	_, err = c.Seek(0, io.SeekStart)
	require.NoError(t, err)
	_, err = c.Write(newHash[:])
	require.NoError(t, err)

	// Also write beyond the original file.
	_, err = c.Seek(32, io.SeekStart)
	require.NoError(t, err)
	_, err = c.Write(newHash[:])
	require.NoError(t, err)

	// Discard.
	c.Discard()

	// Cache should be empty.
	require.Equal(t, 0, c.cache.count())

	// maxWritten should be reset to baseSize.
	require.Equal(t, c.baseSize, c.maxWritten)

	// Read from offset 0 should return the original hash (from underlying).
	_, err = c.Seek(0, io.SeekStart)
	require.NoError(t, err)
	var got [32]byte
	n, err := c.Read(got[:])
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
	_, err := underlying.Write(stale[:])
	require.NoError(t, err)

	c, err := newCachedRWS(underlying, 32, 0, underlying.Size())
	require.NoError(t, err)

	// Write a fresh hash at the same offset.
	fresh := testHashFromInt(2)
	_, err = c.Seek(0, io.SeekStart)
	require.NoError(t, err)
	_, err = c.Write(fresh[:])
	require.NoError(t, err)

	// Read at the same offset should return the fresh hash.
	_, err = c.Seek(0, io.SeekStart)
	require.NoError(t, err)
	var got [32]byte
	_, err = c.Read(got[:])
	require.NoError(t, err)
	require.Equal(t, fresh, Hash(got))
}
