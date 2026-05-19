//go:build !unix

package mmapfile

import (
	"encoding/binary"
	"os"
)

// fileFallback wraps *os.File so it satisfies the File interface on
// non-unix platforms where syscall.Mmap is unavailable.
type fileFallback struct{ *os.File }

func (f fileFallback) HashAt(off int64) ([32]byte, error) {
	var h [32]byte
	_, err := f.ReadAt(h[:], off)
	return h, err
}

func (f fileFallback) PutHashAt(hash [32]byte, off int64) error {
	_, err := f.WriteAt(hash[:], off)
	return err
}

func (f fileFallback) PutUint32At(val uint32, off int64) error {
	var buf [4]byte
	binary.LittleEndian.PutUint32(buf[:], val)
	_, err := f.WriteAt(buf[:], off)
	return err
}

// Open returns the raw *os.File on non-unix platforms where
// syscall.Mmap is not available.
func Open(f *os.File, size int64) (File, error) {
	return fileFallback{f}, nil
}
