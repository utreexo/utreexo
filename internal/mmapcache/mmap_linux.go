//go:build linux

package mmapcache

import "syscall"

// mmapAnon allocates an anonymous private memory region of the given size
// via mmap. MAP_NORESERVE avoids counting the reservation against the
// kernel's overcommit limit, allowing large virtual mappings that are
// only backed by physical pages on first write.
func mmapAnon(size int) ([]byte, error) {
	return syscall.Mmap(
		-1, 0, size,
		syscall.PROT_READ|syscall.PROT_WRITE,
		syscall.MAP_PRIVATE|syscall.MAP_ANONYMOUS|syscall.MAP_NORESERVE,
	)
}

// mmapGrow allocates a larger anonymous region, copies old data into it,
// and releases the old region. Growth is rare (doubling from 1MB) so the
// copy cost is negligible.
func mmapGrow(old []byte, newSize int) ([]byte, error) {
	new, err := mmapAnon(newSize)
	if err != nil {
		return nil, err
	}
	copy(new, old)
	mmapRelease(old)
	return new, nil
}

// mmapReplace releases the old region and allocates a fresh zeroed
// region of the same size.
func mmapReplace(old []byte) ([]byte, error) {
	size := len(old)
	mmapRelease(old)
	return mmapAnon(size)
}

// mmapRelease unmaps a region previously allocated by mmapAnon.
func mmapRelease(data []byte) {
	syscall.Munmap(data)
}
