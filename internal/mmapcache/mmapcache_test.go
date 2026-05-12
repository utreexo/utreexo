package mmapcache

import (
	"encoding/binary"
	"fmt"
	"math/rand"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"
)

func newTestStore(t *testing.T, entrySize int, maxBytes int64) *Store {
	t.Helper()
	s, err := New(entrySize, maxBytes)
	require.NoError(t, err)
	t.Cleanup(func() { s.Close() })
	return s
}

func TestNew(t *testing.T) {
	tests := []struct {
		name      string
		entrySize int
		maxBytes  int64
		wantErr   bool
	}{
		{name: "valid", entrySize: 32, maxBytes: 1024, wantErr: false},
		{name: "zero entry size", entrySize: 0, maxBytes: 1024, wantErr: true},
		{name: "negative entry size", entrySize: -1, maxBytes: 1024, wantErr: true},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s, err := New(tt.entrySize, tt.maxBytes)
			if tt.wantErr {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
				s.Close()
			}
		})
	}
}

func TestEntrySize(t *testing.T) {
	tests := []struct {
		name      string
		entrySize int
	}{
		{name: "4 bytes", entrySize: 4},
		{name: "8 bytes", entrySize: 8},
		{name: "32 bytes", entrySize: 32},
		{name: "64 bytes", entrySize: 64},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := newTestStore(t, tt.entrySize, 1<<20)
			require.Equal(t, tt.entrySize, s.EntrySize())
		})
	}
}

func TestPutGet(t *testing.T) {
	const entrySize = 8

	tests := []struct {
		name    string
		offsets []int64
	}{
		{name: "single slot", offsets: []int64{0}},
		{name: "adjacent slots", offsets: []int64{0, entrySize, 2 * entrySize}},
		{name: "sparse slots", offsets: []int64{0, 100 * entrySize, 1000 * entrySize}},
		{name: "large offset", offsets: []int64{1_000_000 * entrySize}},
		{name: "reverse order", offsets: []int64{3 * entrySize, 2 * entrySize, entrySize, 0}},
		{name: "across word boundary", offsets: []int64{63 * entrySize, 64 * entrySize, 65 * entrySize}},
		{name: "many entries", offsets: []int64{0, entrySize, 2 * entrySize, 3 * entrySize, 4 * entrySize, 5 * entrySize, 6 * entrySize, 7 * entrySize}},
		{name: "many large offsets", offsets: []int64{500_000 * entrySize, 600_000 * entrySize, 700_000 * entrySize, 800_000 * entrySize, 900_000 * entrySize, 1_000_000 * entrySize}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := newTestStore(t, entrySize, 1<<20)

			for i, off := range tt.offsets {
				buf := make([]byte, entrySize)
				binary.LittleEndian.PutUint64(buf, uint64(i+1))
				err := s.Put(off, buf)
				require.NoError(t, err)
			}

			for i, off := range tt.offsets {
				got, ok := s.Get(off)
				require.True(t, ok, "Get(%d) returned false", off)
				v := binary.LittleEndian.Uint64(got)
				require.Equal(t, uint64(i+1), v, "Get(%d)", off)
			}
		})
	}
}

func TestGetMiss(t *testing.T) {
	const entrySize = 8

	tests := []struct {
		name      string
		putOffset int64
		getOffset int64
		shouldPut bool
	}{
		{name: "empty store", getOffset: 0, shouldPut: false},
		{name: "unwritten gap", putOffset: 0, getOffset: entrySize, shouldPut: true},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := newTestStore(t, entrySize, 1<<20)
			if tt.shouldPut {
				err := s.Put(tt.putOffset, make([]byte, entrySize))
				require.NoError(t, err)
			}
			_, ok := s.Get(tt.getOffset)
			require.False(t, ok, "Get(%d) should return false", tt.getOffset)
		})
	}
}

func TestPutOverwrite(t *testing.T) {
	const entrySize = 8
	s := newTestStore(t, entrySize, 1<<20)

	buf := make([]byte, entrySize)
	buf[0] = 0xAA
	s.Put(0, buf)
	require.Equal(t, 1, s.Count())

	buf[0] = 0xBB
	s.Put(0, buf)

	got, ok := s.Get(0)
	require.True(t, ok)
	require.Equal(t, byte(0xBB), got[0])
	require.Equal(t, 1, s.Count())
}

func TestClear(t *testing.T) {
	const entrySize = 8

	tests := []struct {
		name     string
		putSlots []int
	}{
		{name: "empty store", putSlots: nil},
		{name: "single entry", putSlots: []int{0}},
		{name: "multiple entries", putSlots: []int{0, 1, 2, 3, 4}},
		{name: "sparse entries", putSlots: []int{0, 100, 1000}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := newTestStore(t, entrySize, 1<<20)
			for _, slot := range tt.putSlots {
				s.Put(int64(slot*entrySize), make([]byte, entrySize))
			}

			s.Clear()

			require.Equal(t, 0, s.Count())
			for _, slot := range tt.putSlots {
				_, ok := s.Get(int64(slot * entrySize))
				require.False(t, ok, "slot %d still accessible after Clear", slot)
			}

			// ForEach should visit nothing.
			s.ForEach(func(offset int64, data []byte) {
				t.Fatal("ForEach visited an entry after Clear")
			})
		})
	}
}

func TestClearThenReuse(t *testing.T) {
	const entrySize = 8

	tests := []struct {
		name      string
		preClear  byte
		postClear byte
		putOffset int64
		wantCount int
	}{
		{name: "reuse same slot", preClear: 1, postClear: 2, putOffset: 0, wantCount: 1},
		{name: "reuse different value", preClear: 0xAA, postClear: 0xBB, putOffset: 0, wantCount: 1},
		{name: "reuse non-zero offset", preClear: 1, postClear: 2, putOffset: 3 * entrySize, wantCount: 1},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := newTestStore(t, entrySize, 1<<20)

			buf := make([]byte, entrySize)
			buf[0] = tt.preClear
			s.Put(tt.putOffset, buf)
			s.Clear()

			require.Equal(t, 0, s.Count(), "Count() should be 0 after Clear")
			_, ok := s.Get(tt.putOffset)
			require.False(t, ok, "entry should not be accessible after Clear")

			buf[0] = tt.postClear
			s.Put(tt.putOffset, buf)

			got, ok := s.Get(tt.putOffset)
			require.True(t, ok, "expected hit after re-insert")
			require.Equal(t, tt.postClear, got[0])
			require.Equal(t, tt.wantCount, s.Count())
		})
	}
}

func TestForEach(t *testing.T) {
	const entrySize = 8

	tests := []struct {
		name     string
		putSlots []int
	}{
		{name: "empty", putSlots: nil},
		{name: "single", putSlots: []int{0}},
		{name: "contiguous", putSlots: []int{0, 1, 2}},
		{name: "sparse", putSlots: []int{0, 10, 100}},
		{name: "across word boundary", putSlots: []int{0, 63, 64, 127, 128}},
		{name: "sparse reverse", putSlots: []int{100, 10, 0}},
		{name: "across word boundary reverse", putSlots: []int{128, 127, 64, 63, 0}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := newTestStore(t, entrySize, 1<<20)

			expect := make(map[int64]uint64)
			for _, slot := range tt.putSlots {
				off := int64(slot * entrySize)
				buf := make([]byte, entrySize)
				binary.LittleEndian.PutUint64(buf, uint64(slot))
				s.Put(off, buf)
				expect[off] = uint64(slot)
			}

			visited := make(map[int64]uint64)
			s.ForEach(func(offset int64, data []byte) {
				visited[offset] = binary.LittleEndian.Uint64(data)
			})

			require.Equal(t, len(expect), len(visited))
			for off, want := range expect {
				got, ok := visited[off]
				require.True(t, ok, "offset %d not visited", off)
				require.Equal(t, want, got, "offset %d", off)
			}
		})
	}
}

func TestOverflowed(t *testing.T) {
	const entrySize = 8

	tests := []struct {
		name     string
		maxBytes int64
		inserts  int
		want     bool
	}{
		{name: "under limit", maxBytes: 24, inserts: 2, want: false},
		{name: "at limit", maxBytes: 24, inserts: 3, want: false},
		{name: "over limit", maxBytes: 24, inserts: 4, want: true},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := newTestStore(t, entrySize, tt.maxBytes)
			for i := 0; i < tt.inserts; i++ {
				s.Put(int64(i*entrySize), make([]byte, entrySize))
			}
			require.Equal(t, tt.want, s.Overflowed())
		})
	}
}

func TestPutWrongSize(t *testing.T) {
	const entrySize = 8

	tests := []struct {
		name    string
		dataLen int
		wantErr bool
	}{
		{name: "correct size", dataLen: 8, wantErr: false},
		{name: "too short", dataLen: 4, wantErr: true},
		{name: "too long", dataLen: 16, wantErr: true},
		{name: "empty", dataLen: 0, wantErr: true},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := newTestStore(t, entrySize, 1<<20)
			err := s.Put(0, make([]byte, tt.dataLen))
			if tt.wantErr {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
			}
		})
	}
}

func TestAliasesInternalStorage(t *testing.T) {
	const entrySize = 8

	t.Run("Get", func(t *testing.T) {
		s := newTestStore(t, entrySize, 1<<20)

		buf := make([]byte, entrySize)
		binary.LittleEndian.PutUint64(buf, 42)
		s.Put(0, buf)

		got, ok := s.Get(0)
		require.True(t, ok)
		require.Equal(t, uint64(42), binary.LittleEndian.Uint64(got))

		// Mutate the returned slice.
		binary.LittleEndian.PutUint64(got, 99)

		// The mutation should be visible through a second Get since it aliases storage.
		got2, ok := s.Get(0)
		require.True(t, ok)
		require.Equal(t, uint64(99), binary.LittleEndian.Uint64(got2))
	})

	t.Run("ForEach", func(t *testing.T) {
		s := newTestStore(t, entrySize, 1<<20)

		buf := make([]byte, entrySize)
		binary.LittleEndian.PutUint64(buf, 1)
		s.Put(0, buf)

		// Mutate via ForEach callback.
		s.ForEach(func(offset int64, data []byte) {
			binary.LittleEndian.PutUint64(data, 100)
		})

		got, ok := s.Get(0)
		require.True(t, ok)
		require.Equal(t, uint64(100), binary.LittleEndian.Uint64(got))
	})
}

func TestUnalignedOffset(t *testing.T) {
	const entrySize = 8
	s := newTestStore(t, entrySize, 1<<20)

	buf := make([]byte, entrySize)
	binary.LittleEndian.PutUint64(buf, 42)
	s.Put(0, buf)

	// An unaligned offset rounds down via integer division, mapping to slot 0.
	got, ok := s.Get(3)
	require.True(t, ok, "unaligned offset should map to the same slot via integer division")
	require.Equal(t, uint64(42), binary.LittleEndian.Uint64(got))
}

func TestLargeScale(t *testing.T) {
	const entrySize = 8
	const n = 5000
	s := newTestStore(t, entrySize, int64(n*entrySize))

	// Insert n entries at random-ish slots spread across many bitmap words.
	rng := rand.New(rand.NewSource(12345))
	slots := make([]int, n)
	seen := make(map[int]struct{})
	for i := 0; i < n; i++ {
		for {
			slot := rng.Intn(100_000)
			if _, dup := seen[slot]; !dup {
				seen[slot] = struct{}{}
				slots[i] = slot
				break
			}
		}
		off := int64(slots[i] * entrySize)
		buf := make([]byte, entrySize)
		binary.LittleEndian.PutUint64(buf, uint64(slots[i]))
		s.Put(off, buf)
	}
	require.Equal(t, n, s.Count())

	// Verify all entries via Get.
	for _, slot := range slots {
		got, ok := s.Get(int64(slot * entrySize))
		require.True(t, ok, "slot %d missing", slot)
		require.Equal(t, uint64(slot), binary.LittleEndian.Uint64(got))
	}

	// Verify ForEach visits exactly n entries.
	visited := 0
	s.ForEach(func(offset int64, data []byte) { visited++ })
	require.Equal(t, n, visited)

	// Clear, verify empty.
	s.Clear()
	require.Equal(t, 0, s.Count())
	s.ForEach(func(offset int64, data []byte) {
		t.Fatal("ForEach visited entry after Clear")
	})
}

// TestConcurrentDisjointOffsets verifies the documented contract that
// Put and Get on disjoint slots may run concurrently without external
// synchronization, including when those slots share bitmap words.
//
// Writer slots are even, reader slots are odd, and both are partitioned
// round-robin across goroutines. Every bitmap word therefore contains
// bits for both writers and readers, so Get atomic-loads race with Put
// CAS-updates on the SAME word — the property the package claims to
// support. A start-gate channel releases all 2*N goroutines at once so
// the race window covers the full run.
//
// Run with -race to catch any data races on the bitmaps or data region.
func TestConcurrentDisjointOffsets(t *testing.T) {
	const (
		entrySize         = 32
		numGoroutines     = 16
		slotsPerGoroutine = 2048
	)

	s := newTestStore(t, entrySize, 1<<30)

	// Distinct payload schemes: pre-population writes [slot, 0, 0, 0];
	// writers write [slot, writerMagic, 0, 0]. The marker proves a
	// reader-slot Get cannot accidentally pass when the writer no-ops or
	// when bytes from a writer slot leak across — both would change the
	// second uint64 away from its expected value.
	const writerMagic uint64 = 0xC0FFEEC0FFEEC0FF
	encodeReader := func(slot int) []byte {
		buf := make([]byte, entrySize)
		binary.LittleEndian.PutUint64(buf, uint64(slot))
		return buf
	}
	encodeWriter := func(slot int) []byte {
		buf := make([]byte, entrySize)
		binary.LittleEndian.PutUint64(buf, uint64(slot))
		binary.LittleEndian.PutUint64(buf[8:], writerMagic)
		return buf
	}

	// Slot layout: pair (g, i) maps to base = 2*(g + i*N). The writer for
	// goroutine g owns `base` (even); the reader for goroutine g owns
	// `base+1` (odd). Adjacent slots belong to different goroutines and
	// different roles, so every bitmap word is shared across roles.
	writerSlots := make([][]int, numGoroutines)
	readerSlots := make([][]int, numGoroutines)
	for g := 0; g < numGoroutines; g++ {
		writerSlots[g] = make([]int, slotsPerGoroutine)
		readerSlots[g] = make([]int, slotsPerGoroutine)
		for i := 0; i < slotsPerGoroutine; i++ {
			base := 2 * (g + i*numGoroutines)
			writerSlots[g][i] = base
			readerSlots[g][i] = base + 1
		}
	}

	offset := func(slot int) int64 { return int64(slot) * int64(entrySize) }

	// Pre-populate reader slots so concurrent Gets have a defined value
	// to verify. Disjoint from all writer slots.
	for g := 0; g < numGoroutines; g++ {
		for _, slot := range readerSlots[g] {
			require.NoError(t, s.Put(offset(slot), encodeReader(slot)))
		}
	}

	var wg sync.WaitGroup
	errs := make(chan error, 2*numGoroutines)

	// Start gate: every goroutine blocks on <-start until the main thread
	// closes it, so all 2*N goroutines begin work at the same instant
	// rather than the first ones running to completion before the last
	// ones spawn.
	start := make(chan struct{})

	for g := 0; g < numGoroutines; g++ {
		slots := writerSlots[g]
		wg.Add(1)
		go func() {
			defer wg.Done()
			<-start
			for _, slot := range slots {
				if err := s.Put(offset(slot), encodeWriter(slot)); err != nil {
					errs <- fmt.Errorf("Put(slot=%d): %w", slot, err)
					return
				}
			}
		}()
	}
	for g := 0; g < numGoroutines; g++ {
		slots := readerSlots[g]
		wg.Add(1)
		go func() {
			defer wg.Done()
			<-start
			for _, slot := range slots {
				got, ok := s.Get(offset(slot))
				if !ok {
					errs <- fmt.Errorf("Get(slot=%d): missing", slot)
					return
				}
				gotSlot := binary.LittleEndian.Uint64(got[:8])
				gotMark := binary.LittleEndian.Uint64(got[8:16])
				if gotSlot != uint64(slot) || gotMark != 0 {
					errs <- fmt.Errorf("Get(slot=%d): got slot=%d mark=%#x, want slot=%d mark=0",
						slot, gotSlot, gotMark, slot)
					return
				}
			}
		}()
	}

	close(start)
	wg.Wait()
	close(errs)
	for err := range errs {
		t.Error(err)
	}
	if t.Failed() {
		return
	}

	// All writer slots must carry the writer's distinct marker, proving
	// the bytes came from a Put rather than residual state. Count must
	// reflect both writer and reader insertions.
	require.Equal(t, 2*numGoroutines*slotsPerGoroutine, s.Count())
	for g := 0; g < numGoroutines; g++ {
		for _, slot := range writerSlots[g] {
			got, ok := s.Get(offset(slot))
			require.True(t, ok, "writer slot %d missing", slot)
			require.Equal(t, encodeWriter(slot), got, "writer slot %d", slot)
		}
	}
}

// TestCountTracksDirtyNotPresence verifies that Count tracks dirty
// transitions, not presence transitions. After resetDirty, presence
// is preserved but the dirty bitmap and totalCount are zeroed, so
// re-Putting an already-present slot must re-dirty it and bump Count.
// Catches a bug where totalCount.Add lives in the presence CAS branch:
// a re-Put would find presence already set, skip the increment, and
// leave Count at 0 despite the slot being dirty again.
func TestCountTracksDirtyNotPresence(t *testing.T) {
	const entrySize = 8
	s := newTestStore(t, entrySize, 1<<20)

	require.NoError(t, s.Put(0, make([]byte, entrySize)))
	require.Equal(t, 1, s.Count())

	s.resetDirty()
	require.Equal(t, 0, s.Count())

	// Slot 0 is still present (resetDirty leaves presence alone) but
	// no longer dirty. Re-putting must re-dirty and bump Count.
	require.NoError(t, s.Put(0, make([]byte, entrySize)))
	require.Equal(t, 1, s.Count(), "Count must track dirty bits, not presence")
}
