package utreexo

import (
	"testing"
)

func TestCacheMap32(t *testing.T) {
	// Test with 1MB cache
	cms := newCacheMap32(1024 * 1024)

	if len(cms.maps) == 0 {
		t.Fatal("expected at least one map")
	}

	if cms.entrySize() != 32 {
		t.Fatalf("expected entrySize=32, got %d", cms.entrySize())
	}

	// Insert 1000 entries
	for i := range 1000 {
		var data [32]byte
		data[0] = byte(i)
		cms.put32(int64(i), data)
	}

	if cms.count() != 1000 {
		t.Fatalf("expected 1000 entries, got %d", cms.count())
	}

	// Verify we can get them back
	for i := range 1000 {
		data, ok := cms.get(int64(i))
		if !ok {
			t.Fatalf("expected to find key %d", i)
		}
		if data[0] != byte(i) {
			t.Fatalf("expected data[0]=%d, got %d", byte(i), data[0])
		}
	}

	// Delete half
	for i := range 500 {
		cms.delete(int64(i))
	}

	if cms.count() != 500 {
		t.Fatalf("expected 500 entries after delete, got %d", cms.count())
	}

	// Verify deleted entries are gone
	for i := range 500 {
		_, ok := cms.get(int64(i))
		if ok {
			t.Fatalf("expected key %d to be deleted", i)
		}
	}

	// Clear and verify
	cms.clear()
	if cms.count() != 0 {
		t.Fatalf("expected 0 entries after clear, got %d", cms.count())
	}
}

func TestCacheMap8(t *testing.T) {
	cms := newCacheMap8(1024 * 1024)

	if cms.entrySize() != 8 {
		t.Fatalf("expected entrySize=8, got %d", cms.entrySize())
	}

	for i := range 1000 {
		var data [8]byte
		data[0] = byte(i)
		cms.put8(int64(i), data)
	}

	if cms.count() != 1000 {
		t.Fatalf("expected 1000 entries, got %d", cms.count())
	}

	for i := range 1000 {
		data, ok := cms.get(int64(i))
		if !ok {
			t.Fatalf("expected to find key %d", i)
		}
		if data[0] != byte(i) {
			t.Fatalf("expected data[0]=%d, got %d", byte(i), data[0])
		}
	}
}

func TestCacheMap4(t *testing.T) {
	cms := newCacheMap4(1024 * 1024)

	if cms.entrySize() != 4 {
		t.Fatalf("expected entrySize=4, got %d", cms.entrySize())
	}

	for i := range 1000 {
		var data [4]byte
		data[0] = byte(i)
		cms.put4(int64(i), data)
	}

	if cms.count() != 1000 {
		t.Fatalf("expected 1000 entries, got %d", cms.count())
	}

	for i := range 1000 {
		data, ok := cms.get(int64(i))
		if !ok {
			t.Fatalf("expected to find key %d", i)
		}
		if data[0] != byte(i) {
			t.Fatalf("expected data[0]=%d, got %d", byte(i), data[0])
		}
	}
}

func TestCacheMapOverflow(t *testing.T) {
	// Create a very small cache that will overflow
	cms := newCacheMap32(1024) // Only 1KB

	// Fill beyond capacity to trigger overflow
	for i := range 1000 {
		var data [32]byte
		data[0] = byte(i)
		cms.put32(int64(i), data)
	}

	// Should have overflowed
	if !cms.overflowed() {
		t.Fatal("expected cache to overflow")
	}

	// But all entries should still be retrievable
	for i := range 1000 {
		data, ok := cms.get(int64(i))
		if !ok {
			t.Fatalf("expected to find key %d", i)
		}
		if data[0] != byte(i) {
			t.Fatalf("expected data[0]=%d, got %d", byte(i), data[0])
		}
	}
}

func TestCacheMapDeleteAbove(t *testing.T) {
	cms := newCacheMap32(1024 * 1024)

	// Insert entries with offsets 0-999
	for i := range 1000 {
		var data [32]byte
		cms.put32(int64(i), data)
	}

	// Delete all entries at offset >= 500
	cms.deleteAbove(500)

	// Should have 500 entries left
	if cms.count() != 500 {
		t.Fatalf("expected 500 entries, got %d", cms.count())
	}

	// Entries 0-499 should exist
	for i := range 500 {
		_, ok := cms.get(int64(i))
		if !ok {
			t.Fatalf("expected key %d to exist", i)
		}
	}

	// Entries 500-999 should not exist
	for i := range 500 {
		_, ok := cms.get(int64(i + 500))
		if ok {
			t.Fatalf("expected key %d to be deleted", i+500)
		}
	}
}

func TestCacheMapForEach(t *testing.T) {
	cms := newCacheMap32(1024 * 1024)

	// Insert entries
	for i := range 100 {
		var data [32]byte
		data[0] = byte(i)
		cms.put32(int64(i), data)
	}

	// Count entries via forEach
	count := 0
	cms.forEach(func(offset int64, data []byte) {
		count++
		if data[0] != byte(offset) {
			t.Fatalf("expected data[0]=%d, got %d", byte(offset), data[0])
		}
	})

	if count != 100 {
		t.Fatalf("expected forEach to visit 100 entries, got %d", count)
	}
}

func TestCacheMapNoDuplicates(t *testing.T) {
	cms := newCacheMap32(1024 * 1024)

	// Insert same key twice with different values
	var data1, data2 [32]byte
	data1[0] = 1
	data2[0] = 2

	cms.put32(42, data1)
	cms.put32(42, data2)

	// Should only have 1 entry
	if cms.count() != 1 {
		t.Fatalf("expected 1 entry, got %d", cms.count())
	}

	// Should have the second value
	data, ok := cms.get(42)
	if !ok {
		t.Fatal("expected to find key 42")
	}
	if data[0] != 2 {
		t.Fatalf("expected data[0]=2, got %d", data[0])
	}
}
