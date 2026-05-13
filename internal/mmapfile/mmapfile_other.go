//go:build !unix

package mmapfile

import "os"

// fileFallback wraps *os.File so it satisfies the File interface on
// non-unix platforms where syscall.Mmap is unavailable.
type fileFallback struct{ *os.File }

func (f fileFallback) HashAt(off int64) ([32]byte, error) {
	var h [32]byte
	_, err := f.ReadAt(h[:], off)
	return h, err
}

// Open returns the raw *os.File on non-unix platforms where
// syscall.Mmap is not available.
func Open(f *os.File, size int64) (File, error) {
	return fileFallback{f}, nil
}
