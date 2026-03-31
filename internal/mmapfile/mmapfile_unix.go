//go:build unix

package mmapfile

import (
	"errors"
	"fmt"
	"io"
	"os"
	"syscall"
)

var errClosed = errors.New("mmapFile: use after close")

// mmapFile wraps a memory-mapped file region and implements the File
// interface. Using mmap replaces per-call pread/pwrite syscalls with
// direct memory copies.
type mmapFile struct {
	data []byte   // mmap'd region; nil after Close
	file *os.File // kept for Sync (fsync) and final close
	pos  int64
	size int64
}

// Open memory-maps the first size bytes of f with PROT_READ|PROT_WRITE
// and MAP_SHARED so that writes are visible to the OS page cache and can
// be flushed with fsync. The caller must have already sized f (e.g. via
// Truncate). The returned File owns f and will close it on Close.
func Open(f *os.File, size int64) (File, error) {
	if size <= 0 {
		return nil, fmt.Errorf("mmap %s: size must be > 0, got %d", f.Name(), size)
	}
	data, err := syscall.Mmap(
		int(f.Fd()), 0, int(size),
		syscall.PROT_READ|syscall.PROT_WRITE,
		syscall.MAP_SHARED,
	)
	if err != nil {
		return nil, fmt.Errorf("mmap %s: %w", f.Name(), err)
	}
	return &mmapFile{
		data: data,
		file: f,
		size: size,
	}, nil
}

func (m *mmapFile) ReadAt(p []byte, off int64) (int, error) {
	if m.data == nil {
		return 0, errClosed
	}
	if off < 0 || off >= m.size {
		return 0, io.EOF
	}
	n := copy(p, m.data[off:m.size])
	if n < len(p) {
		return n, io.EOF
	}
	return n, nil
}

func (m *mmapFile) WriteAt(p []byte, off int64) (int, error) {
	if m.data == nil {
		return 0, errClosed
	}
	if off < 0 || off >= m.size {
		return 0, fmt.Errorf("mmapFile: writeAt at %d beyond size %d", off, m.size)
	}
	n := copy(m.data[off:m.size], p)
	if n < len(p) {
		return n, fmt.Errorf("mmapFile: short writeAt at %d (wrote %d of %d)", off, n, len(p))
	}
	return n, nil
}

func (m *mmapFile) Read(p []byte) (int, error) {
	n, err := m.ReadAt(p, m.pos)
	m.pos += int64(n)
	return n, err
}

func (m *mmapFile) Write(p []byte) (int, error) {
	if m.data == nil {
		return 0, errClosed
	}
	start := m.pos
	if start < 0 || start >= m.size {
		return 0, fmt.Errorf("mmapFile: write at %d beyond size %d", start, m.size)
	}
	n := copy(m.data[start:m.size], p)
	m.pos += int64(n)
	if n < len(p) {
		return n, fmt.Errorf("mmapFile: short write at %d (wrote %d of %d)", start, n, len(p))
	}
	return n, nil
}

func (m *mmapFile) Seek(offset int64, whence int) (int64, error) {
	if m.data == nil {
		return 0, errClosed
	}
	var abs int64
	switch whence {
	case io.SeekStart:
		abs = offset
	case io.SeekCurrent:
		abs = m.pos + offset
	case io.SeekEnd:
		abs = m.size + offset
	default:
		return 0, fmt.Errorf("mmapFile: invalid whence %d", whence)
	}
	if abs < 0 {
		return 0, fmt.Errorf("mmapFile: negative seek position %d", abs)
	}
	m.pos = abs
	return abs, nil
}

// Sync flushes the mapped pages to stable storage via fsync.
func (m *mmapFile) Sync() error {
	if m.data == nil {
		return errClosed
	}
	return m.file.Sync()
}

// Close unmaps the region and closes the underlying file.
func (m *mmapFile) Close() error {
	if m.data == nil {
		return errClosed
	}
	err := syscall.Munmap(m.data)
	m.data = nil
	if err2 := m.file.Close(); err == nil {
		err = err2
	}
	return err
}
