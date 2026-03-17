package utreexo

import (
	"testing"
)

// cacheStoreFactories returns constructors for each cacheStore implementation
// so every test exercises both.
func cacheStoreFactories(t *testing.T, entrySize int, maxBytes int64) []struct {
	name string
	cs   cacheStore
} {
	t.Helper()
	mmapCS, err := newMmapCacheStore(entrySize, maxBytes)
	if err != nil {
		t.Fatal(err)
	}
	return []struct {
		name string
		cs   cacheStore
	}{
		{"Page", newPageCacheStore(entrySize, maxBytes)},
		{"Mmap", mmapCS},
	}
}

func TestCacheStorePutGet(t *testing.T) {
	for _, f := range cacheStoreFactories(t, 32, 1<<20) {
		t.Run(f.name, func(t *testing.T) {
			cs := f.cs
			for i := range 1000 {
				var data [32]byte
				data[0] = byte(i)
				cs.put(int64(i)*32, data[:])
			}

			if cs.count() != 1000 {
				t.Fatalf("expected 1000 entries, got %d", cs.count())
			}

			for i := range 1000 {
				data, ok := cs.get(int64(i) * 32)
				if !ok {
					t.Fatalf("expected to find offset %d", i*32)
				}
				if data[0] != byte(i) {
					t.Fatalf("expected data[0]=%d, got %d", byte(i), data[0])
				}
			}
		})
	}
}

func TestCacheStorePutGet4(t *testing.T) {
	for _, f := range cacheStoreFactories(t, 4, 1<<20) {
		t.Run(f.name, func(t *testing.T) {
			cs := f.cs
			for i := range 1000 {
				var data [4]byte
				data[0] = byte(i)
				cs.put(int64(i)*4, data[:])
			}

			if cs.count() != 1000 {
				t.Fatalf("expected 1000 entries, got %d", cs.count())
			}

			for i := range 1000 {
				data, ok := cs.get(int64(i) * 4)
				if !ok {
					t.Fatalf("expected to find offset %d", i*4)
				}
				if data[0] != byte(i) {
					t.Fatalf("expected data[0]=%d, got %d", byte(i), data[0])
				}
			}
		})
	}
}

func TestCacheStorePutGet8(t *testing.T) {
	for _, f := range cacheStoreFactories(t, 8, 1<<20) {
		t.Run(f.name, func(t *testing.T) {
			cs := f.cs
			for i := range 1000 {
				var data [8]byte
				data[0] = byte(i)
				cs.put(int64(i)*8, data[:])
			}

			if cs.count() != 1000 {
				t.Fatalf("expected 1000 entries, got %d", cs.count())
			}

			for i := range 1000 {
				data, ok := cs.get(int64(i) * 8)
				if !ok {
					t.Fatalf("expected to find offset %d", i*8)
				}
				if data[0] != byte(i) {
					t.Fatalf("expected data[0]=%d, got %d", byte(i), data[0])
				}
			}
		})
	}
}

func TestCacheStoreDelete(t *testing.T) {
	for _, f := range cacheStoreFactories(t, 32, 1<<20) {
		t.Run(f.name, func(t *testing.T) {
			cs := f.cs
			for i := range 1000 {
				var data [32]byte
				data[0] = byte(i)
				cs.put(int64(i)*32, data[:])
			}

			// Delete first half.
			for i := range 500 {
				cs.delete(int64(i) * 32)
			}

			if cs.count() != 500 {
				t.Fatalf("expected 500 entries after delete, got %d", cs.count())
			}

			// Deleted entries should be gone.
			for i := range 500 {
				_, ok := cs.get(int64(i) * 32)
				if ok {
					t.Fatalf("expected offset %d to be deleted", i*32)
				}
			}

			// Remaining entries should be intact.
			for i := 500; i < 1000; i++ {
				data, ok := cs.get(int64(i) * 32)
				if !ok {
					t.Fatalf("expected to find offset %d", i*32)
				}
				if data[0] != byte(i) {
					t.Fatalf("expected data[0]=%d, got %d", byte(i), data[0])
				}
			}
		})
	}
}

func TestCacheStoreDeleteAbove(t *testing.T) {
	for _, f := range cacheStoreFactories(t, 32, 1<<20) {
		t.Run(f.name, func(t *testing.T) {
			cs := f.cs
			for i := range 1000 {
				var data [32]byte
				cs.put(int64(i)*32, data[:])
			}

			// Delete all entries at offset >= 500*32.
			cs.deleteAbove(500 * 32)

			if cs.count() != 500 {
				t.Fatalf("expected 500 entries, got %d", cs.count())
			}

			for i := range 500 {
				_, ok := cs.get(int64(i) * 32)
				if !ok {
					t.Fatalf("expected offset %d to exist", i*32)
				}
			}

			for i := 500; i < 1000; i++ {
				_, ok := cs.get(int64(i) * 32)
				if ok {
					t.Fatalf("expected offset %d to be deleted", i*32)
				}
			}
		})
	}
}

func TestCacheStoreClear(t *testing.T) {
	for _, f := range cacheStoreFactories(t, 32, 1<<20) {
		t.Run(f.name, func(t *testing.T) {
			cs := f.cs
			for i := range 100 {
				var data [32]byte
				cs.put(int64(i)*32, data[:])
			}

			cs.clear()

			if cs.count() != 0 {
				t.Fatalf("expected 0 entries after clear, got %d", cs.count())
			}

			// Re-insert should work fine after clear.
			var data [32]byte
			data[0] = 42
			cs.put(0, data[:])
			got, ok := cs.get(0)
			if !ok {
				t.Fatal("expected to find entry after re-insert")
			}
			if got[0] != 42 {
				t.Fatalf("expected 42, got %d", got[0])
			}
		})
	}
}

func TestCacheStoreForEach(t *testing.T) {
	for _, f := range cacheStoreFactories(t, 32, 1<<20) {
		t.Run(f.name, func(t *testing.T) {
			cs := f.cs
			for i := range 100 {
				var data [32]byte
				data[0] = byte(i)
				cs.put(int64(i)*32, data[:])
			}

			visited := make(map[int64]byte)
			cs.forEach(func(offset int64, data []byte) {
				visited[offset] = data[0]
			})

			if len(visited) != 100 {
				t.Fatalf("expected forEach to visit 100 entries, got %d", len(visited))
			}

			for i := range 100 {
				v, ok := visited[int64(i)*32]
				if !ok {
					t.Fatalf("forEach missed offset %d", i*32)
				}
				if v != byte(i) {
					t.Fatalf("at offset %d: expected %d, got %d", i*32, byte(i), v)
				}
			}
		})
	}
}

func TestCacheStoreOverflowed(t *testing.T) {
	// Use a tiny budget: 1KB with 32-byte entries = 32 entries max.
	for _, f := range cacheStoreFactories(t, 32, 1024) {
		t.Run(f.name, func(t *testing.T) {
			cs := f.cs
			if cs.overflowed() {
				t.Fatal("should not overflow when empty")
			}

			// Fill beyond capacity.
			for i := range 100 {
				var data [32]byte
				cs.put(int64(i)*32, data[:])
			}

			if !cs.overflowed() {
				t.Fatal("expected cache to overflow")
			}

			// All entries should still be retrievable.
			for i := range 100 {
				_, ok := cs.get(int64(i) * 32)
				if !ok {
					t.Fatalf("expected to find offset %d", i*32)
				}
			}
		})
	}
}

func TestCacheStoreNoDuplicates(t *testing.T) {
	for _, f := range cacheStoreFactories(t, 32, 1<<20) {
		t.Run(f.name, func(t *testing.T) {
			cs := f.cs

			var data1, data2 [32]byte
			data1[0] = 1
			data2[0] = 2

			cs.put(42*32, data1[:])
			cs.put(42*32, data2[:])

			if cs.count() != 1 {
				t.Fatalf("expected 1 entry, got %d", cs.count())
			}

			data, ok := cs.get(42 * 32)
			if !ok {
				t.Fatal("expected to find entry")
			}
			if data[0] != 2 {
				t.Fatalf("expected data[0]=2, got %d", data[0])
			}
		})
	}
}

func TestCacheStoreEntrySize(t *testing.T) {
	for _, es := range []int{4, 8, 32} {
		for _, f := range cacheStoreFactories(t, es, 1<<20) {
			t.Run(f.name, func(t *testing.T) {
				if f.cs.entrySize() != es {
					t.Fatalf("expected entrySize=%d, got %d", es, f.cs.entrySize())
				}
			})
		}
	}
}
