package swisstable

import "syscall"

// mmapFlags are the flags passed to syscall.Mmap for shared, read-write mappings.
// MAP_POPULATE pre-faults pages on Linux, avoiding page faults on first access.
const mmapFlags = syscall.MAP_SHARED | syscall.MAP_POPULATE

// mmapAnon allocates an anonymous memory region of the given size via mmap.
// The returned slice is not tracked by Go's GC, so it must be freed with
// munmapAnon. MAP_NORESERVE avoids reserving swap space upfront.
func mmapAnon(size int) ([]byte, error) {
	return syscall.Mmap(-1, 0, size,
		syscall.PROT_READ|syscall.PROT_WRITE,
		syscall.MAP_PRIVATE|syscall.MAP_ANONYMOUS|syscall.MAP_NORESERVE)
}

// munmapAnon releases an anonymous mmap region allocated by mmapAnon.
func munmapAnon(b []byte) {
	syscall.Munmap(b)
}
