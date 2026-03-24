//go:build !unix

package swisstable

import (
	"io"
	"os"
)

// miniHash is the first 12 bytes of a 256 bit hash.
type miniHash [12]byte

// mini takes the first 12 bytes of a hash and outputs a miniHash.
func mini(h [32]byte) miniHash {
	var m miniHash
	copy(m[:], h[:12])
	return m
}

// SwissPositionMap is a simple map-backed fallback for non-unix platforms
// where mmap is not available. It provides the same public API as the
// mmap-backed Swiss Table implementation but does not persist to disk.
type SwissPositionMap struct {
	m        map[miniHash]uint64
	dataFile io.ReaderAt
}

// NewSwissPositionMap creates a new in-memory position map.
// On non-unix platforms this always returns needsRebuild=true since the
// map is not persisted. The ctrlFile and slotsFile are unused (closed
// immediately if non-nil).
func NewSwissPositionMap(ctrlFile, slotsFile *os.File, expectedEntries uint64, consistencyHash [32]byte, dataFile io.ReaderAt, posMask uint64) (*SwissPositionMap, bool, error) {
	return &SwissPositionMap{
		m:        make(map[miniHash]uint64, expectedEntries),
		dataFile: dataFile,
	}, true, nil
}

// Get looks up a hash and returns its packed position.
func (m *SwissPositionMap) Get(hash [32]byte) (uint64, bool, error) {
	v, ok := m.m[mini(hash)]
	return v, ok, nil
}

// Set stores a hash -> packed position mapping.
func (m *SwissPositionMap) Set(hash [32]byte, packed uint64) error {
	m.m[mini(hash)] = packed
	return nil
}

// Delete removes a hash from the map.
func (m *SwissPositionMap) Delete(hash [32]byte) (bool, error) {
	key := mini(hash)
	if _, ok := m.m[key]; !ok {
		return false, nil
	}
	delete(m.m, key)
	return true, nil
}

// Count returns the number of entries.
func (m *SwissPositionMap) Count() uint64 {
	return uint64(len(m.m))
}

// ForEach iterates over all entries.
func (m *SwissPositionMap) ForEach(fn func(packed uint64)) {
	for _, v := range m.m {
		fn(v)
	}
}

// Close is a no-op on non-unix platforms.
func (m *SwissPositionMap) Close() error {
	return nil
}

// SetConsistencyHash is a no-op on non-unix platforms since the map
// is not persisted.
func (m *SwissPositionMap) SetConsistencyHash(hash [32]byte) error {
	return nil
}

// RebuildEntry holds a hash and packed value for bulk insertion.
type RebuildEntry struct {
	hash   [32]byte
	packed uint64
}

// PrepareEntry computes a RebuildEntry for bulk rebuild.
func (m *SwissPositionMap) PrepareEntry(hash [32]byte, packed uint64) RebuildEntry {
	return RebuildEntry{
		hash:   hash,
		packed: packed,
	}
}

// PrepareRebuild clears the map for a fresh bulk rebuild.
func (m *SwissPositionMap) PrepareRebuild() {
	clear(m.m)
}

// InsertBatch inserts a batch of entries into the map.
func (m *SwissPositionMap) InsertBatch(entries []RebuildEntry) error {
	for _, e := range entries {
		m.m[mini(e.hash)] = e.packed
	}
	return nil
}

// ApplyConsistencyHash is a no-op on non-unix platforms.
func (m *SwissPositionMap) ApplyConsistencyHash(hash [32]byte) error { return nil }

// PendingCtrlOverlay returns nil on non-unix platforms (no overlay).
func (m *SwissPositionMap) PendingCtrlOverlay() map[uint64]byte { return nil }

// PendingSlotsOverlay returns nil on non-unix platforms (no overlay).
func (m *SwissPositionMap) PendingSlotsOverlay() map[uint64]uint64 { return nil }

// ForEachPendingCtrl is a no-op on non-unix platforms.
func (m *SwissPositionMap) ForEachPendingCtrl(fn func(fileOffset int64, value byte)) {}

// ForEachPendingSlot is a no-op on non-unix platforms.
func (m *SwissPositionMap) ForEachPendingSlot(fn func(fileOffset int64, value uint64)) {}

// ApplyPending is a no-op on non-unix platforms.
func (m *SwissPositionMap) ApplyPending() error { return nil }

// SyncFiles is a no-op on non-unix platforms.
func (m *SwissPositionMap) SyncFiles() error { return nil }

// ClearPending is a no-op on non-unix platforms.
func (m *SwissPositionMap) ClearPending() {}

// DiscardPending is a no-op on non-unix platforms.
func (m *SwissPositionMap) DiscardPending() {}
