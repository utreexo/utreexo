//go:build unix

package utreexo

import "syscall"

// mmapAnon allocates an anonymous private memory region of the given size
// via mmap. The region is not backed by any file and lives outside the Go
// heap, so the garbage collector does not scan it.
func mmapAnon(size int) ([]byte, error) {
	return syscall.Mmap(
		-1, 0, size,
		syscall.PROT_READ|syscall.PROT_WRITE,
		syscall.MAP_PRIVATE|syscall.MAP_ANONYMOUS,
	)
}

// mmapRelease unmaps a region previously allocated by mmapAnon.
func mmapRelease(data []byte) {
	syscall.Munmap(data)
}
