// Package mmapfile provides a memory-mapped file implementation.
// On unix, Open returns an mmap-backed file; on other platforms it
// falls back to the raw *os.File.
package mmapfile

import (
	"io"
)

// File is the interface returned by Open. It combines the read/write/seek
// and random-read capabilities needed by the forest data file, plus
// Close for resource cleanup.
//
// Sync is discovered dynamically via type assertion by the WAL's
// syncFile helper, so it is not part of this interface.
type File interface {
	io.ReadWriteSeeker
	io.ReaderAt
	io.WriterAt
	io.Closer
}
