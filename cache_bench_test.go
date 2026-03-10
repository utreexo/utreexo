package utreexo

import (
	"fmt"
	"math/rand"
	"testing"
)

// cacheFactory creates a fresh cacheStore for benchmarking.
type cacheFactory struct {
	name string
	make func(entrySize int, maxBytes int64) cacheStore
}

var cacheFactories = []cacheFactory{
	{"Page", func(es int, mb int64) cacheStore {
		return newPageCacheStore(es, mb)
	}},
	{"Mmap", func(es int, mb int64) cacheStore {
		return newMmapCacheStore(es, mb)
	}},
}

// generateForestOffsets returns n offsets simulating a forest data file:
// most writes land in leaf row (dense, low offsets), with parents spread
// across higher rows at sparser offsets.
func generateForestOffsets(n int, entrySize int, rng *rand.Rand) []int64 {
	offsets := make([]int64, n)
	for i := range n {
		// ~70% leaf row (offsets 0..10M), ~20% row 1 (offsets 10M..15M),
		// ~10% higher rows (offsets 15M..20M).
		r := rng.Float64()
		switch {
		case r < 0.70:
			offsets[i] = int64(rng.Intn(10_000_000/entrySize)) * int64(entrySize)
		case r < 0.90:
			offsets[i] = int64(10_000_000) + int64(rng.Intn(5_000_000/entrySize))*int64(entrySize)
		default:
			offsets[i] = int64(15_000_000) + int64(rng.Intn(5_000_000/entrySize))*int64(entrySize)
		}
	}
	return offsets
}

// ---------- Benchmarks ----------

func BenchmarkCachePutSeq(b *testing.B) {
	const entrySize = 32
	const maxBytes = 64 << 20
	data := [32]byte{1, 2, 3, 4}

	for _, f := range cacheFactories {
		b.Run(f.name, func(b *testing.B) {
			c := f.make(entrySize, maxBytes)
			b.ResetTimer()
			for i := range b.N {
				c.put(int64(i)*entrySize, data[:])
			}
		})
	}
}

func BenchmarkCachePutRandom(b *testing.B) {
	const entrySize = 32
	const maxBytes = 64 << 20
	data := [32]byte{1, 2, 3, 4}
	rng := rand.New(rand.NewSource(42))
	offsets := generateForestOffsets(1_000_000, entrySize, rng)

	for _, f := range cacheFactories {
		b.Run(f.name, func(b *testing.B) {
			c := f.make(entrySize, maxBytes)
			b.ResetTimer()
			for i := range b.N {
				c.put(offsets[i%len(offsets)], data[:])
			}
		})
	}
}

func BenchmarkCacheGetHit(b *testing.B) {
	const entrySize = 32
	const maxBytes = 64 << 20
	const numEntries = 500_000
	data := [32]byte{1, 2, 3, 4}
	rng := rand.New(rand.NewSource(42))
	offsets := generateForestOffsets(numEntries, entrySize, rng)

	for _, f := range cacheFactories {
		b.Run(f.name, func(b *testing.B) {
			c := f.make(entrySize, maxBytes)
			for _, off := range offsets {
				c.put(off, data[:])
			}
			b.ResetTimer()
			for i := range b.N {
				c.get(offsets[i%numEntries])
			}
		})
	}
}

func BenchmarkCacheGetMiss(b *testing.B) {
	const entrySize = 32
	const maxBytes = 64 << 20
	const numEntries = 500_000
	data := [32]byte{1, 2, 3, 4}
	rng := rand.New(rand.NewSource(42))
	offsets := generateForestOffsets(numEntries, entrySize, rng)

	// Offsets that are NOT in the cache.
	missOffsets := make([]int64, numEntries)
	for i := range missOffsets {
		missOffsets[i] = int64(30_000_000) + int64(i)*entrySize
	}

	for _, f := range cacheFactories {
		b.Run(f.name, func(b *testing.B) {
			c := f.make(entrySize, maxBytes)
			for _, off := range offsets {
				c.put(off, data[:])
			}
			b.ResetTimer()
			for i := range b.N {
				c.get(missOffsets[i%numEntries])
			}
		})
	}
}

func BenchmarkCachePutOverwrite(b *testing.B) {
	const entrySize = 32
	const maxBytes = 64 << 20
	const numEntries = 500_000
	data := [32]byte{1, 2, 3, 4}
	rng := rand.New(rand.NewSource(42))
	offsets := generateForestOffsets(numEntries, entrySize, rng)

	for _, f := range cacheFactories {
		b.Run(f.name, func(b *testing.B) {
			c := f.make(entrySize, maxBytes)
			// Pre-fill.
			for _, off := range offsets {
				c.put(off, data[:])
			}
			b.ResetTimer()
			// Overwrite the same keys.
			for i := range b.N {
				c.put(offsets[i%numEntries], data[:])
			}
		})
	}
}

func BenchmarkCacheForEach(b *testing.B) {
	const entrySize = 32
	const maxBytes = 64 << 20
	data := [32]byte{1, 2, 3, 4}
	rng := rand.New(rand.NewSource(42))

	for _, count := range []int{10_000, 100_000, 500_000} {
		offsets := generateForestOffsets(count, entrySize, rng)
		b.Run(fmt.Sprintf("n=%d", count), func(b *testing.B) {
			for _, f := range cacheFactories {
				b.Run(f.name, func(b *testing.B) {
					c := f.make(entrySize, maxBytes)
					for _, off := range offsets {
						c.put(off, data[:])
					}
					b.ResetTimer()
					for range b.N {
						c.forEach(func(offset int64, d []byte) {})
					}
				})
			}
		})
	}
}

func BenchmarkCacheClear(b *testing.B) {
	const entrySize = 32
	const maxBytes = 64 << 20
	data := [32]byte{1, 2, 3, 4}
	rng := rand.New(rand.NewSource(42))

	for _, count := range []int{10_000, 100_000} {
		offsets := generateForestOffsets(count, entrySize, rng)
		b.Run(fmt.Sprintf("n=%d", count), func(b *testing.B) {
			for _, f := range cacheFactories {
				b.Run(f.name, func(b *testing.B) {
					c := f.make(entrySize, maxBytes)
					for range b.N {
						for _, off := range offsets {
							c.put(off, data[:])
						}
						c.clear()
					}
				})
			}
		})
	}
}

func BenchmarkCacheMixed(b *testing.B) {
	// Simulate a realistic workload: 60% puts, 40% gets.
	const entrySize = 32
	const maxBytes = 64 << 20
	const numEntries = 500_000
	data := [32]byte{1, 2, 3, 4}
	rng := rand.New(rand.NewSource(42))
	offsets := generateForestOffsets(numEntries, entrySize, rng)

	for _, f := range cacheFactories {
		b.Run(f.name, func(b *testing.B) {
			c := f.make(entrySize, maxBytes)
			b.ResetTimer()
			for i := range b.N {
				off := offsets[i%numEntries]
				if i%5 < 3 {
					c.put(off, data[:])
				} else {
					c.get(off)
				}
			}
		})
	}
}

func BenchmarkCacheMemoryOverhead(b *testing.B) {
	// This benchmark measures allocation overhead by filling the cache
	// to a fixed size and reporting allocs/op.
	const entrySize = 32
	const maxBytes = 64 << 20
	const numEntries = 10_000
	data := [32]byte{1, 2, 3, 4}
	rng := rand.New(rand.NewSource(42))
	offsets := generateForestOffsets(numEntries, entrySize, rng)

	for _, f := range cacheFactories {
		b.Run(f.name, func(b *testing.B) {
			b.ReportAllocs()
			for range b.N {
				c := f.make(entrySize, maxBytes)
				for _, off := range offsets {
					c.put(off, data[:])
				}
				c.clear()
			}
		})
	}
}
