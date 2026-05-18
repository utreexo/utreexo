//go:build linux

package mmapcache

import "syscall"

// mmapAnon allocates an anonymous private memory region of the given size
// via mmap. The region is not backed by any file and lives outside the Go
// heap, so the garbage collector does not scan it.
func mmapAnon(size int) ([]byte, error) {
	return syscall.Mmap(
		-1, // fd: no backing file (required for MAP_ANONYMOUS)
		0,  // offset: irrelevant without a backing file
		size,
		syscall.PROT_READ|syscall.PROT_WRITE, // pages are readable and writable
		// MAP_PRIVATE:     changes are private to this process (copy-on-write)
		// MAP_ANONYMOUS:   not backed by a file; memory is zeroed
		// MAP_NORESERVE:   don't reserve swap upfront; physical memory is allocated
		//                  lazily as pages are touched, allowing a large virtual
		//                  address space without requiring that much RAM or swap
		syscall.MAP_PRIVATE|syscall.MAP_ANONYMOUS|syscall.MAP_NORESERVE,
	)
}

// mmapRelease unmaps a region previously allocated by mmapAnon.
// Munmap errors are ignored; they indicate a programming bug (e.g. double
// unmap) and cannot be meaningfully recovered from.
func mmapRelease(data []byte) {
	_ = syscall.Munmap(data)
}

// madviseDontNeed tells the kernel to drop the physical pages backing the
// given range. The virtual mapping stays intact; subsequent accesses fault
// in fresh zero-filled pages. Used by Store.Clear to release resident
// memory after a logical reset without re-mmapping the address space.
// Errors are ignored: MADV_DONTNEED is advisory and a failure only means
// the kernel kept pages it was free to drop, which is benign.
func madviseDontNeed(data []byte) {
	_ = syscall.Madvise(data, syscall.MADV_DONTNEED)
}
