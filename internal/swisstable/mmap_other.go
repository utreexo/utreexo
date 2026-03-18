//go:build unix && !linux

package swisstable

import "syscall"

// mmapFlags are the flags passed to syscall.Mmap for shared, read-write mappings.
// MAP_POPULATE is Linux-only, so other platforms use MAP_SHARED alone.
const mmapFlags = syscall.MAP_SHARED

// mmapAnon allocates an anonymous memory region of the given size via mmap.
// The returned slice is not tracked by Go's GC, so it must be freed with
// munmapAnon.
func mmapAnon(size int) ([]byte, error) {
	return syscall.Mmap(-1, 0, size,
		syscall.PROT_READ|syscall.PROT_WRITE,
		syscall.MAP_PRIVATE|syscall.MAP_ANON)
}

// munmapAnon releases an anonymous mmap region allocated by mmapAnon.
func munmapAnon(b []byte) {
	syscall.Munmap(b)
}
