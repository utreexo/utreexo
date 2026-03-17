//go:build !linux

package utreexo

// newMmapCacheStore returns a page-based cache on non-linux platforms
// where anonymous mmap is not used.
func newMmapCacheStore(entrySize int, maxBytes int64) (*pageCacheStore, error) {
	return newPageCacheStore(entrySize, maxBytes), nil
}
