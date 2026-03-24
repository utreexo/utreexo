//go:build unix

package swisstable

import (
	"crypto/sha256"
	"encoding/binary"
	"fmt"
	"os"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"
)

// Test-local position packing constants matching the values used by forest.go.
const (
	testPositionBits = 47
	testPositionMask = (1 << testPositionBits) - 1
)

// testHashFromInt creates a deterministic hash from an integer for testing.
func testHashFromInt(n int) [32]byte {
	var buf [8]byte
	binary.BigEndian.PutUint64(buf[:], uint64(n))
	return sha256.Sum256(buf[:])
}

// packPosIndex packs a position and add-index into a single uint64.
func packPosIndex(pos uint64, addIndex int32) uint64 {
	return (uint64(uint32(addIndex)) << testPositionBits) | (pos & testPositionMask)
}

func TestMatchH2(t *testing.T) {
	// helper: build a 16-byte ctrl group filled with `fill`, then
	// overwrite specific positions with `target`.
	makeCtrl := func(fill byte, target byte, positions []int) [16]byte {
		var ctrl [16]byte
		for i := range ctrl {
			ctrl[i] = fill
		}
		for _, p := range positions {
			ctrl[p] = target
		}
		return ctrl
	}

	// helper: convert a list of set-bit positions to a uint16 mask.
	maskFrom := func(positions []int) uint16 {
		var m uint16
		for _, p := range positions {
			m |= 1 << p
		}
		return m
	}

	tests := []struct {
		name      string
		ctrl      [16]byte
		h2        byte
		wantMatch []int // bit positions expected in the returned mask
	}{
		{
			name:      "no matches when all slots differ",
			ctrl:      makeCtrl(0b10000000, 0b10000000, nil),
			h2:        0b10000101,
			wantMatch: nil,
		},
		{
			name:      "single match at position 0",
			ctrl:      makeCtrl(0b10000000, 0b10000101, []int{0}),
			h2:        0b10000101,
			wantMatch: []int{0},
		},
		{
			name:      "single match at position 15",
			ctrl:      makeCtrl(0b10000000, 0b10000101, []int{15}),
			h2:        0b10000101,
			wantMatch: []int{15},
		},
		{
			name:      "multiple matches",
			ctrl:      makeCtrl(0b10000000, 0b10000101, []int{0, 5, 15}),
			h2:        0b10000101,
			wantMatch: []int{0, 5, 15},
		},
		{
			name:      "all 16 slots match",
			ctrl:      makeCtrl(0b10000101, 0b10000101, nil),
			h2:        0b10000101,
			wantMatch: []int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
		},
		{
			name:      "all slots empty - no match for full h2",
			ctrl:      makeCtrl(0b00000000, 0b00000000, nil),
			h2:        0b10000101,
			wantMatch: nil,
		},
		{
			name:      "match minimum full value 0b10000000",
			ctrl:      makeCtrl(0b11111111, 0b10000000, []int{3, 9}),
			h2:        0b10000000,
			wantMatch: []int{3, 9},
		},
		{
			name:      "match maximum full value 0b11111111",
			ctrl:      makeCtrl(0b10000000, 0b11111111, []int{7, 14}),
			h2:        0b11111111,
			wantMatch: []int{7, 14},
		},
		{
			name:      "match h2=0b00000000 finds empty slots",
			ctrl:      makeCtrl(0b10000000, 0b00000000, []int{2, 10}),
			h2:        0b00000000,
			wantMatch: []int{2, 10},
		},
		{
			name: "match among mixed ctrl bytes",
			ctrl: [16]byte{
				0b10000101, 0b00000000, 0b01111111, 0b10000101,
				0b10000000, 0b10000001, 0b10000010, 0b10000101,
				0b10000011, 0b10000100, 0b10000110, 0b10000111,
				0b10001000, 0b10001001, 0b10001010, 0b10000101,
			},
			h2:        0b10000101,
			wantMatch: []int{0, 3, 7, 15},
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			got := matchH2(tc.ctrl[:], tc.h2)
			require.Equal(t, maskFrom(tc.wantMatch), got)
		})
	}
}

func TestMatchEmpty(t *testing.T) {
	maskFrom := func(positions []int) uint16 {
		var m uint16
		for _, p := range positions {
			m |= 1 << p
		}
		return m
	}

	fillCtrl := func(val byte) [16]byte {
		var ctrl [16]byte
		for i := range ctrl {
			ctrl[i] = val
		}
		return ctrl
	}

	tests := []struct {
		name      string
		ctrl      [16]byte
		wantMatch []int
	}{
		{
			name:      "all empty",
			ctrl:      fillCtrl(ctrlEmpty),
			wantMatch: []int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
		},
		{
			name:      "no empty - all full",
			ctrl:      fillCtrl(0b10000000),
			wantMatch: nil,
		},
		{
			name:      "no empty - all deleted",
			ctrl:      fillCtrl(ctrlDeleted),
			wantMatch: nil,
		},
		{
			name:      "single empty at position 0",
			ctrl:      func() [16]byte { c := fillCtrl(0b10000000); c[0] = ctrlEmpty; return c }(),
			wantMatch: []int{0},
		},
		{
			name:      "single empty at position 15",
			ctrl:      func() [16]byte { c := fillCtrl(0b10000000); c[15] = ctrlEmpty; return c }(),
			wantMatch: []int{15},
		},
		{
			name:      "two empty slots",
			ctrl:      func() [16]byte { c := fillCtrl(0b10000000); c[2] = ctrlEmpty; c[10] = ctrlEmpty; return c }(),
			wantMatch: []int{2, 10},
		},
		{
			name: "empty among deleted and full",
			ctrl: func() [16]byte {
				c := fillCtrl(0b10000000)
				c[1] = ctrlDeleted // deleted - not empty
				c[4] = ctrlEmpty   // empty
				c[7] = ctrlDeleted // deleted - not empty
				c[12] = ctrlEmpty  // empty
				return c
			}(),
			wantMatch: []int{4, 12},
		},
		{
			name: "alternating empty and full",
			ctrl: func() [16]byte {
				var c [16]byte
				for i := range c {
					if i%2 == 0 {
						c[i] = ctrlEmpty
					} else {
						c[i] = 0b10000101
					}
				}
				return c
			}(),
			wantMatch: []int{0, 2, 4, 6, 8, 10, 12, 14},
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			got := matchEmpty(tc.ctrl[:])
			require.Equal(t, maskFrom(tc.wantMatch), got)
		})
	}
}

func TestMatchEmptyOrDeleted(t *testing.T) {
	maskFrom := func(positions []int) uint16 {
		var m uint16
		for _, p := range positions {
			m |= 1 << p
		}
		return m
	}

	fillCtrl := func(val byte) [16]byte {
		var ctrl [16]byte
		for i := range ctrl {
			ctrl[i] = val
		}
		return ctrl
	}

	tests := []struct {
		name      string
		ctrl      [16]byte
		wantMatch []int
	}{
		{
			name:      "all full - no matches",
			ctrl:      fillCtrl(0b10000000),
			wantMatch: nil,
		},
		{
			name:      "all empty - all match",
			ctrl:      fillCtrl(ctrlEmpty),
			wantMatch: []int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
		},
		{
			name:      "all deleted - all match",
			ctrl:      fillCtrl(ctrlDeleted),
			wantMatch: []int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
		},
		{
			name: "mix of empty and deleted both match",
			ctrl: func() [16]byte {
				c := fillCtrl(0b10000000)
				c[1] = ctrlEmpty
				c[7] = ctrlDeleted
				c[14] = ctrlEmpty
				return c
			}(),
			wantMatch: []int{1, 7, 14},
		},
		{
			name: "only deleted slots match",
			ctrl: func() [16]byte {
				c := fillCtrl(0b10000000)
				c[0] = ctrlDeleted
				c[8] = ctrlDeleted
				c[15] = ctrlDeleted
				return c
			}(),
			wantMatch: []int{0, 8, 15},
		},
		{
			name: "only empty slots match",
			ctrl: func() [16]byte {
				c := fillCtrl(0b10000000)
				c[5] = ctrlEmpty
				c[11] = ctrlEmpty
				return c
			}(),
			wantMatch: []int{5, 11},
		},
		{
			name: "various non-full values in low range all match",
			ctrl: func() [16]byte {
				c := fillCtrl(0b10000000)
				c[0] = 0b00000000 // empty
				c[3] = 0b00000001 // low bit set, high bit clear -> matches
				c[6] = 0b01111110 // high bit clear -> matches
				c[9] = 0b01111111 // deleted
				return c
			}(),
			wantMatch: []int{0, 3, 6, 9},
		},
		{
			name: "full slots with different h2 values never match",
			ctrl: [16]byte{
				0b10000000, 0b10000001, 0b10010000, 0b10100000,
				0b10110000, 0b11000000, 0b11010000, 0b11100000,
				0b11110000, 0b11111111, 0b10000101, 0b10010010,
				0b10101010, 0b10111011, 0b11001100, 0b11011101,
			},
			// all have high bit set
			wantMatch: nil,
		},
		{
			name: "alternating empty/deleted and full",
			ctrl: func() [16]byte {
				var c [16]byte
				for i := range c {
					switch i % 3 {
					case 0:
						c[i] = ctrlEmpty
					case 1:
						c[i] = ctrlDeleted
					case 2:
						c[i] = 0b10000101
					}
				}
				return c
			}(),
			wantMatch: []int{0, 1, 3, 4, 6, 7, 9, 10, 12, 13, 15},
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			got := matchEmptyOrDeleted(tc.ctrl[:])
			require.Equal(t, maskFrom(tc.wantMatch), got)
		})
	}
}

func TestSwissPositionMapBasic(t *testing.T) {
	tests := []struct {
		name       string
		numEntries int
		capacity   uint64
	}{
		{"low collision", 3, 100},
		{"high collision", 60, 20}, // small capacity forces linear probing
		{"large low collision", 10000, 20000},
		{"large high collision", 10000, 100}, // extreme overload forces many resizes
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			m, hashes := newTestSwissMap(t, tt.numEntries, tt.capacity)

			// Insert all entries.
			for i, h := range hashes {
				require.NoError(t, m.Set(h, packPosIndex(uint64(i), 0)))
			}
			require.Equal(t, uint64(tt.numEntries), m.Count())

			// Get them back.
			for i, h := range hashes {
				packed, ok, err := m.Get(h)
				require.NoError(t, err)
				require.True(t, ok, "entry %d should exist", i)
				require.Equal(t, packPosIndex(uint64(i), 0), packed)
			}

			// Non-existent key.
			_, ok, err := m.Get(testHashFromInt(tt.numEntries + 1))
			require.NoError(t, err)
			require.False(t, ok)

			// Delete even-indexed entries to create tombstones.
			for i := 0; i < tt.numEntries; i += 2 {
				ok, err := m.Delete(hashes[i])
				require.NoError(t, err, "delete entry %d", i)
				require.True(t, ok, "delete entry %d", i)
			}
			surviving := uint64(tt.numEntries / 2)
			require.Equal(t, surviving, m.Count())

			// Deleted entries should not be found.
			for i := 0; i < tt.numEntries; i += 2 {
				_, ok, err := m.Get(hashes[i])
				require.NoError(t, err, "entry %d", i)
				require.False(t, ok, "deleted entry %d should not be found", i)
			}

			// Surviving entries should still exist.
			for i := 1; i < tt.numEntries; i += 2 {
				_, ok, err := m.Get(hashes[i])
				require.NoError(t, err, "entry %d", i)
				require.True(t, ok, "entry %d should still exist", i)
			}

			// Re-Set surviving entries with a different packed value.
			// Verifies Set updates in-place rather than inserting
			// duplicates when tombstones exist.
			for i := 1; i < tt.numEntries; i += 2 {
				require.NoError(t, m.Set(hashes[i], packPosIndex(uint64(i), 1)))
			}
			require.Equal(t, surviving, m.Count(),
				"count should not change when updating existing entries")

			// ForEach count must agree with Count().
			var forEachCount uint64
			m.ForEach(func(packed uint64) { forEachCount++ })
			require.Equal(t, surviving, forEachCount,
				"ForEach entry count must match Count()")

			// Every surviving entry should return the updated packed value.
			for i := 1; i < tt.numEntries; i += 2 {
				packed, ok, err := m.Get(hashes[i])
				require.NoError(t, err, "entry %d", i)
				require.True(t, ok, "entry %d should still exist", i)
				require.Equal(t, packPosIndex(uint64(i), 1), packed,
					"entry %d should have the updated packed value", i)
			}
		})
	}
}

// openTestFile creates a temporary file and registers cleanup.
func openTestFile(t *testing.T, name string) *os.File {
	t.Helper()
	f, err := os.OpenFile(t.TempDir()+"/"+name, os.O_RDWR|os.O_CREATE, 0644)
	require.NoError(t, err)
	t.Cleanup(func() { f.Close() })
	return f
}

// newTestSwissMap creates a SwissPositionMap backed by temp files with the
// given number of test hashes written to the data file.
func newTestSwissMap(t *testing.T, numEntries int, capacity uint64) (*SwissPositionMap, [][32]byte) {
	t.Helper()

	dataFile, err := os.Create(t.TempDir() + "/data")
	require.NoError(t, err)
	t.Cleanup(func() { dataFile.Close() })

	hashes := make([][32]byte, numEntries)
	for i := range numEntries {
		hashes[i] = testHashFromInt(i)
		_, err := dataFile.Write(hashes[i][:])
		require.NoError(t, err)
	}
	dataFile.Seek(0, 0)

	ctrlFile := openTestFile(t, "ctrl")
	slotsFile := openTestFile(t, "slots")
	m, _, err := NewSwissPositionMap(
		ctrlFile, slotsFile,
		capacity, [32]byte{}, dataFile, testPositionMask,
	)
	require.NoError(t, err)
	t.Cleanup(func() { m.Close() })

	return m, hashes
}

func TestSwissPositionMapConsistency(t *testing.T) {
	hashes := [][32]byte{testHashFromInt(1), testHashFromInt(2), testHashFromInt(3)}
	savedHash := [32]byte{1, 2, 3}

	// buildTable creates a valid table with 3 entries and savedHash,
	// then closes everything so the caller can corrupt files before reopening.
	buildTable := func(t *testing.T, ctrlPath, slotsPath, dataPath string) {
		t.Helper()
		dataFile, err := os.Create(dataPath)
		require.NoError(t, err)
		for _, h := range hashes {
			dataFile.Write(h[:])
		}
		dataFile.Seek(0, 0)

		ctrlFile, err := os.OpenFile(ctrlPath, os.O_RDWR|os.O_CREATE, 0644)
		require.NoError(t, err)
		slotsFile, err := os.OpenFile(slotsPath, os.O_RDWR|os.O_CREATE, 0644)
		require.NoError(t, err)
		m, _, err := NewSwissPositionMap(ctrlFile, slotsFile, 100, [32]byte{}, dataFile, testPositionMask)
		require.NoError(t, err)
		for i, h := range hashes {
			require.NoError(t, m.Set(h, uint64(i)))
		}
		// Apply overlay to files so SetConsistencyHash validates on reopen.
		require.NoError(t, m.ApplyPending())
		m.ClearPending()
		require.NoError(t, m.SetConsistencyHash(savedHash))
		m.Close()
		dataFile.Close()
	}

	tests := []struct {
		name            string
		corrupt         func(t *testing.T, ctrlPath, slotsPath string) // nil = no corruption
		reopenHash      [32]byte
		expectedEntries uint64 // passed to NewSwissPositionMap on reopen
		wantRebuild     bool
		wantCount       uint64
	}{
		{
			name:            "same hash, no corruption",
			reopenHash:      savedHash,
			expectedEntries: 100,
			wantRebuild:     false,
			wantCount:       3,
		},
		{
			name:            "zero hash",
			reopenHash:      [32]byte{},
			expectedEntries: 100,
			wantRebuild:     true,
		},
		{
			name:            "different hash",
			reopenHash:      [32]byte{9, 9, 9},
			expectedEntries: 100,
			wantRebuild:     true,
		},
		{
			name:       "ctrl file truncated",
			reopenHash: savedHash,
			corrupt: func(t *testing.T, ctrlPath, _ string) {
				require.NoError(t, os.Truncate(ctrlPath, 0))
			},
			expectedEntries: 100,
			wantRebuild:     true,
		},
		{
			name:       "slots file truncated",
			reopenHash: savedHash,
			corrupt: func(t *testing.T, _, slotsPath string) {
				require.NoError(t, os.Truncate(slotsPath, 0))
			},
			expectedEntries: 100,
			wantRebuild:     true,
		},
		{
			name:       "ctrl header corrupted",
			reopenHash: savedHash,
			corrupt: func(t *testing.T, ctrlPath, _ string) {
				f, err := os.OpenFile(ctrlPath, os.O_WRONLY, 0644)
				require.NoError(t, err)
				_, err = f.WriteAt([]byte{0xFF, 0xFE, 0xFD}, 0)
				require.NoError(t, err)
				f.Close()
			},
			expectedEntries: 100,
			wantRebuild:     true,
		},
		{
			name:       "slots header corrupted",
			reopenHash: savedHash,
			corrupt: func(t *testing.T, _, slotsPath string) {
				f, err := os.OpenFile(slotsPath, os.O_WRONLY, 0644)
				require.NoError(t, err)
				_, err = f.WriteAt([]byte{0xFF, 0xFE, 0xFD}, 0)
				require.NoError(t, err)
				f.Close()
			},
			expectedEntries: 100,
			wantRebuild:     true,
		},
		{
			name:            "different expectedEntries reuses consistent files",
			reopenHash:      savedHash,
			expectedEntries: 200,
			wantRebuild:     false,
			wantCount:       3,
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			tmpDir := t.TempDir()
			ctrlPath := tmpDir + "/ctrl"
			slotsPath := tmpDir + "/slots"
			dataPath := tmpDir + "/data"
			buildTable(t, ctrlPath, slotsPath, dataPath)

			if tc.corrupt != nil {
				tc.corrupt(t, ctrlPath, slotsPath)
			}

			dataFile, err := os.Open(dataPath)
			require.NoError(t, err)
			defer dataFile.Close()

			ctrlFile, err := os.OpenFile(ctrlPath, os.O_RDWR|os.O_CREATE, 0644)
			require.NoError(t, err)
			slotsFile, err := os.OpenFile(slotsPath, os.O_RDWR|os.O_CREATE, 0644)
			require.NoError(t, err)
			m, needsRebuild, err := NewSwissPositionMap(ctrlFile, slotsFile, tc.expectedEntries, tc.reopenHash, dataFile, testPositionMask)
			require.NoError(t, err)
			defer m.Close()

			require.Equal(t, tc.wantRebuild, needsRebuild)
			require.Equal(t, tc.wantCount, m.Count())
		})
	}
}

func TestSwissPositionMapNilDataFile(t *testing.T) {
	ctrlFile := openTestFile(t, "ctrl")
	slotsFile := openTestFile(t, "slots")
	_, _, err := NewSwissPositionMap(ctrlFile, slotsFile, 10, [32]byte{}, nil, testPositionMask)
	require.Error(t, err)
}

// TestSwissPositionMapResizeConsistencyHash verifies that SetConsistencyHash
// works after resize (i.e. ctrlMmap is updated, not stale).
func TestSwissPositionMapResizeConsistencyHash(t *testing.T) {
	m, hashes := newTestSwissMap(t, 100, 10)

	initialSlots := m.numSlots

	for i, h := range hashes {
		require.NoError(t, m.Set(h, uint64(i)))
	}
	require.Greater(t, m.numSlots, initialSlots, "should have resized")

	// SetConsistencyHash after resize must not panic and must not error.
	// After resize, overlay is cleared and data is in the mmap.
	var setErr error
	require.NotPanics(t, func() {
		setErr = m.SetConsistencyHash([32]byte{0xAB})
	})
	require.NoError(t, setErr)

	// Verify the hash was actually written into the mmap.
	var stored [32]byte
	copy(stored[:], m.ctrlMmap[:32])
	expected := [32]byte{0xAB}
	require.Equal(t, expected, stored, "consistency hash should be readable from ctrlMmap after resize")
}

// TestSwissPositionMapConcurrentGet verifies that concurrent
// Get calls are safe.
func TestSwissPositionMapConcurrentGet(t *testing.T) {
	// Find two hashes that land in different Swiss table buckets so
	// concurrent Get calls exercise independent lookup paths.
	hashA := testHashFromInt(1)
	hashB := testHashFromInt(2)
	for i := 3; ; i++ {
		_, h2a := splitHash(hashA)
		_, h2b := splitHash(hashB)
		if h2a != h2b {
			break
		}
		hashB = testHashFromInt(i)
	}

	posA := uint64(1)
	posB := uint64(3)
	dataSlots := uint64(4)

	// Create a data file with hashes at the packed positions used below.
	// Set(hashA, posA) reads from offset posA*32, Set(hashB, posB) reads from offset posB*32.
	dataPath := t.TempDir() + "/data"
	dataFile, err := os.Create(dataPath)
	require.NoError(t, err)
	defer dataFile.Close()

	hashes := make([][32]byte, dataSlots)
	hashes[posA] = hashA
	hashes[posB] = hashB
	for _, h := range hashes {
		_, err := dataFile.Write(h[:])
		require.NoError(t, err)
	}

	ctrlFile := openTestFile(t, "ctrl")
	slotsFile := openTestFile(t, "slots")
	m, _, err := NewSwissPositionMap(ctrlFile, slotsFile, dataSlots, [32]byte{}, dataFile, testPositionMask)
	require.NoError(t, err)
	defer m.Close()

	require.NoError(t, m.Set(hashA, posA))
	require.NoError(t, m.Set(hashB, posB))

	wg := new(sync.WaitGroup)
	wg.Add(2)
	errs := make(chan error, 2)
	go func() {
		defer wg.Done()
		for range 1000 {
			gotHashA, found, err := m.Get(hashA)
			if err != nil {
				errs <- fmt.Errorf("Get(hashA): %w", err)
				return
			}
			if !found || gotHashA != posA {
				errs <- fmt.Errorf("expected %v, got found=%v hashA=%x", posA, found, gotHashA)
				return
			}

			gotHashB, found, err := m.Get(hashB)
			if err != nil {
				errs <- fmt.Errorf("Get(hashB): %w", err)
				return
			}
			if !found || gotHashB != posB {
				errs <- fmt.Errorf("expected %v, got found=%v hashB=%x", posB, found, gotHashB)
				return
			}
		}
	}()

	go func() {
		defer wg.Done()
		for range 1000 {
			gotHashB, found, err := m.Get(hashB)
			if err != nil {
				errs <- fmt.Errorf("Get(hashB): %w", err)
				return
			}
			if !found || gotHashB != posB {
				errs <- fmt.Errorf("expected %v, got found=%v hashB=%x", posB, found, gotHashB)
				return
			}

			gotHashA, found, err := m.Get(hashA)
			if err != nil {
				errs <- fmt.Errorf("Get(hashA): %w", err)
				return
			}
			if !found || gotHashA != posA {
				errs <- fmt.Errorf("expected %v, got found=%v hashA=%x", posA, found, gotHashA)
				return
			}
		}
	}()

	wg.Wait()
	close(errs)

	for err := range errs {
		require.NoError(t, err)
	}
}

func BenchmarkMatchH2(b *testing.B) {
	ctrl := make([]byte, 16)
	for i := range ctrl {
		ctrl[i] = byte(i) | 0x80
	}
	ctrl[7] = 0x85

	b.ResetTimer()
	for b.Loop() {
		matchH2(ctrl, 0x85)
	}
}

func BenchmarkSwissGet(b *testing.B) {
	tmpDir := b.TempDir()

	// Create data file with 10k hashes
	dataFile, _ := os.Create(tmpDir + "/data")
	numEntries := 10000
	hashes := make([][32]byte, numEntries)
	for i := range numEntries {
		hashes[i] = testHashFromInt(i)
		dataFile.Write(hashes[i][:])
	}
	dataFile.Seek(0, 0)

	ctrlFile, _ := os.OpenFile(tmpDir+"/ctrl", os.O_RDWR|os.O_CREATE, 0644)
	slotsFile, _ := os.OpenFile(tmpDir+"/slots", os.O_RDWR|os.O_CREATE, 0644)
	m, _, _ := NewSwissPositionMap(ctrlFile, slotsFile, uint64(numEntries), [32]byte{}, dataFile, testPositionMask)
	defer m.Close()

	for i, h := range hashes {
		m.Set(h, uint64(i))
	}

	b.ResetTimer()
	for i := range b.N {
		m.Get(hashes[i%numEntries])
	}
}

func BenchmarkSwissSet(b *testing.B) {
	tmpDir := b.TempDir()

	dataFile, _ := os.Create(tmpDir + "/data")
	numEntries := b.N
	if numEntries > 100000 {
		numEntries = 100000
	}

	hashes := make([][32]byte, numEntries)
	for i := range numEntries {
		hashes[i] = testHashFromInt(i)
		dataFile.Write(hashes[i][:])
	}
	dataFile.Seek(0, 0)

	ctrlFile, _ := os.OpenFile(tmpDir+"/ctrl", os.O_RDWR|os.O_CREATE, 0644)
	slotsFile, _ := os.OpenFile(tmpDir+"/slots", os.O_RDWR|os.O_CREATE, 0644)
	m, _, _ := NewSwissPositionMap(ctrlFile, slotsFile, uint64(numEntries), [32]byte{}, dataFile, testPositionMask)
	defer m.Close()

	b.ResetTimer()
	for i := range b.N {
		m.Set(hashes[i%numEntries], uint64(i%numEntries))
	}
}

// BenchmarkGoMapGet benchmarks native Go map for comparison.
func BenchmarkGoMapGet(b *testing.B) {
	type miniHash [12]byte

	numEntries := 10000
	hashes := make([]miniHash, numEntries)
	m := make(map[miniHash]uint64, numEntries)

	for i := range numEntries {
		h := testHashFromInt(i)
		copy(hashes[i][:], h[:12])
		m[hashes[i]] = uint64(i)
	}

	b.ResetTimer()
	for i := range b.N {
		_ = m[hashes[i%numEntries]]
	}
}

// BenchmarkGoMapSet benchmarks native Go map for comparison.
func BenchmarkGoMapSet(b *testing.B) {
	type miniHash [12]byte

	numEntries := 10000
	hashes := make([]miniHash, numEntries)
	m := make(map[miniHash]uint64, numEntries)

	for i := range numEntries {
		h := testHashFromInt(i)
		copy(hashes[i][:], h[:12])
	}

	b.ResetTimer()
	for i := range b.N {
		m[hashes[i%numEntries]] = uint64(i % numEntries)
	}
}
