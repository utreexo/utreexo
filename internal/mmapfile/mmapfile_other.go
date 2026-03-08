//go:build !unix

package mmapfile

import "os"

// Open returns the raw *os.File on non-unix platforms where
// syscall.Mmap is not available.
func Open(f *os.File, size int64) (File, error) {
	return f, nil
}
