//go:build !unix

package utreexo

// mmapAnon returns a heap-allocated byte slice on non-unix platforms
// where anonymous mmap is not available.
func mmapAnon(size int) ([]byte, error) {
	return make([]byte, size), nil
}

// mmapRelease is a no-op on non-unix platforms; the GC reclaims the slice.
func mmapRelease(data []byte) {}
