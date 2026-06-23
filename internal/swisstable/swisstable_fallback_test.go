//go:build !unix

package swisstable

import (
	"testing"

	"github.com/stretchr/testify/require"
)

func TestSwissPositionMapFallbackBasic(t *testing.T) {
	m, needsRebuild, err := NewSwissPositionMap("", "", 100, [32]byte{}, nil, 0)
	require.NoError(t, err)
	require.True(t, needsRebuild, "fallback always needs rebuild")
	defer m.Close()

	h1 := [32]byte{1}
	h2 := [32]byte{2}
	h3 := [32]byte{3}

	// Set
	require.NoError(t, m.Set(h1, 10))
	require.NoError(t, m.Set(h2, 20))
	require.NoError(t, m.Set(h3, 30))
	require.Equal(t, uint64(3), m.Count())

	// Get
	v, ok, err := m.Get(h1)
	require.NoError(t, err)
	require.True(t, ok)
	require.Equal(t, uint64(10), v)

	v, ok, err = m.Get(h2)
	require.NoError(t, err)
	require.True(t, ok)
	require.Equal(t, uint64(20), v)

	// Get non-existent
	_, ok, err = m.Get([32]byte{99})
	require.NoError(t, err)
	require.False(t, ok)

	// Delete
	deleted, err := m.Delete(h2)
	require.NoError(t, err)
	require.True(t, deleted)
	require.Equal(t, uint64(2), m.Count())

	_, ok, err = m.Get(h2)
	require.NoError(t, err)
	require.False(t, ok)

	// Delete non-existent
	deleted, err = m.Delete([32]byte{99})
	require.NoError(t, err)
	require.False(t, deleted)

	// ForEach
	var sum uint64
	m.ForEach(func(packed uint64) {
		sum += packed
	})
	require.Equal(t, uint64(40), sum) // 10 + 30

	// Update existing
	require.NoError(t, m.Set(h1, 100))
	require.Equal(t, uint64(2), m.Count())
	v, ok, err = m.Get(h1)
	require.NoError(t, err)
	require.True(t, ok)
	require.Equal(t, uint64(100), v)

	// BeginBatch + Insert
	batch, err := m.BeginBatch(2)
	require.NoError(t, err)
	require.NoError(t, batch.Insert(h2, 200))
	require.NoError(t, batch.Insert([32]byte{4}, 40))
	require.Equal(t, uint64(4), m.Count())
	v, ok, err = m.Get(h2)
	require.NoError(t, err)
	require.True(t, ok)
	require.Equal(t, uint64(200), v)

	// SetConsistencyHash is a no-op
	require.NoError(t, m.SetConsistencyHash([32]byte{1, 2, 3}))
}
