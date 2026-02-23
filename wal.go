package utreexo

import (
	"encoding/binary"
	"fmt"
	"hash/crc32"
	"io"
)

// WAL coordinates crash-safe writes across multiple cachedRWS instances.
// It uses a write-ahead journal to ensure atomicity: either all buffered
// writes are applied to the underlying files, or none are.
//
// Journal format (all little-endian):
//
//	totalLen  uint64   (byte length of entries block)
//	bestHash  [32]byte (consistency hash, e.g. best block hash)
//	[entries] ...      (totalLen bytes)
//	checksum  uint32   (CRC32-IEEE of totalLen + bestHash + entries)
//
// Each entry:
//
//	fileIdx   uint8    (which underlying file)
//	offset    int64    (byte offset in that file)
//	dataLen   uint32   (length of data)
//	data      []byte   (the actual bytes)
//
// Flush sequence:
//  1. Collect entries from all cachedRWS caches
//  2. Add consistency hash entry (file 3, offset 32)
//  3. Write bestHash + entries + CRC32 checksum to journal
//  4. Sync journal
//  5. Apply entries to underlying files (including consistency hash)
//  6. Sync underlying files
//  7. Clear journal (write totalLen=0, sync)
//  8. Reset cachedRWS caches
//
// Recovery (in NewWAL):
//  1. Read journal; if valid checksum found, replay entries to underlying
//  2. Clear journal
//
// The consistency hash is written to file 3 (metaFile) at offset 32,
// and can be read from there after recovery or normal startup.
type WAL struct {
	journal io.ReadWriteSeeker
	cached  []*cachedRWS
}

// journalEntry represents a single write operation in the WAL journal.
type journalEntry struct {
	fileIdx uint8
	offset  int64
	data    []byte
}

const (
	journalHeaderSize   = 8  // uint64 totalLen
	journalHashSize     = 32 // [32]byte bestHash
	journalChecksumSize = 4  // uint32 CRC32
	entryHeaderSize     = 13 // 1 (fileIdx) + 8 (offset) + 4 (dataLen)
	journalMinSize      = journalHeaderSize + journalHashSize + journalChecksumSize

	metaFileIdx    = 3  // index of the metadata file in the WAL file list
	bestHashOffset = 32 // byte offset of the consistency hash in the metadata file
)

// WALFile represents an underlying file with its entry size and cache config.
type WALFile struct {
	File          ForestFile
	EntrySize     int   // 4, 8, or 32
	MaxCacheBytes int64 // 0 means use default (64MB)
}

// NewWAL creates a WAL coordinating writes across the given underlying files.
// It first recovers any committed but unapplied journal entries, then wraps
// each underlying file in a cachedRWS. Use Cached(i) to get the
// io.ReadWriteSeeker to pass to Forest.
// Each file's MaxCacheBytes sets its memory threshold for signaling flush needed.
// If MaxCacheBytes is 0, a default of 64MB is used.
func NewWAL(journal io.ReadWriteSeeker, files ...WALFile) (*WAL, error) {
	if len(files) != 4 {
		return nil, fmt.Errorf("wal requires exactly 4 files, got %d", len(files))
	}

	underlying := make([]ForestFile, len(files))
	for i, f := range files {
		underlying[i] = f.File
	}

	w := &WAL{
		journal: journal,
		cached:  make([]*cachedRWS, len(files)),
	}

	// Replay any committed journal entries before creating caches,
	// since newCachedRWS reads the underlying file size.
	if err := w.recoverFromJournal(underlying); err != nil {
		return nil, fmt.Errorf("wal recover: %w", err)
	}

	for i, f := range files {
		c, err := newCachedRWS(f.File, f.EntrySize, f.MaxCacheBytes)
		if err != nil {
			return nil, fmt.Errorf("wal wrap file %d: %w", i, err)
		}
		w.cached[i] = c
	}

	return w, nil
}

// Cached returns the cachedRWS for the i-th underlying file.
func (w *WAL) Cached(i int) *cachedRWS {
	return w.cached[i]
}

// Flush atomically commits all cached writes through the journal.
// The bestHash is written to metaFile (file index 3) at offset 32.
func (w *WAL) Flush(bestHash [32]byte) error {
	// Serialize entries directly from caches to avoid intermediate allocations.
	entriesBuf := w.serializeEntries(bestHash)
	totalLen := uint64(len(entriesBuf))

	// Build header.
	var header [journalHeaderSize]byte
	binary.LittleEndian.PutUint64(header[:], totalLen)

	// Compute CRC32 over header + bestHash + entries.
	crc := crc32.NewIEEE()
	crc.Write(header[:])
	crc.Write(bestHash[:])
	crc.Write(entriesBuf)
	var checksumBuf [journalChecksumSize]byte
	binary.LittleEndian.PutUint32(checksumBuf[:], crc.Sum32())

	// Write journal: header + bestHash + entries + checksum.
	if _, err := w.journal.Seek(0, io.SeekStart); err != nil {
		return fmt.Errorf("wal journal seek: %w", err)
	}
	if _, err := w.journal.Write(header[:]); err != nil {
		return fmt.Errorf("wal journal write header: %w", err)
	}
	if _, err := w.journal.Write(bestHash[:]); err != nil {
		return fmt.Errorf("wal journal write bestHash: %w", err)
	}
	if _, err := w.journal.Write(entriesBuf); err != nil {
		return fmt.Errorf("wal journal write entries: %w", err)
	}
	if _, err := w.journal.Write(checksumBuf[:]); err != nil {
		return fmt.Errorf("wal journal write checksum: %w", err)
	}

	// Sync journal to ensure it's durable before touching underlying files.
	if err := syncFile(w.journal); err != nil {
		return fmt.Errorf("wal journal sync: %w", err)
	}

	// Apply directly from caches to underlying files.
	if err := w.applyFromCaches(bestHash); err != nil {
		return fmt.Errorf("wal apply: %w", err)
	}

	// Sync underlying files.
	for i, c := range w.cached {
		if err := syncFile(c.underlying); err != nil {
			return fmt.Errorf("wal sync file %d: %w", i, err)
		}
	}

	// Clear journal.
	if err := w.clearJournal(); err != nil {
		return fmt.Errorf("wal clear journal: %w", err)
	}

	// Reset caches so baseSize reflects the new underlying state.
	for i, c := range w.cached {
		if err := c.resetAfterFlush(); err != nil {
			return fmt.Errorf("wal reset cache %d: %w", i, err)
		}
	}

	return nil
}

// serializeEntries encodes journal entries directly from caches into a byte slice,
// avoiding intermediate allocations. Includes the bestHash entry for metaFile.
func (w *WAL) serializeEntries(bestHash [32]byte) []byte {
	// Pre-calculate total size.
	size := 0
	for _, c := range w.cached {
		size += c.cache.count() * (entryHeaderSize + c.cache.entrySize())
	}
	// Add bestHash entry for metaFile.
	size += entryHeaderSize + 32

	buf := make([]byte, 0, size)

	// Serialize entries from each cache.
	for i, c := range w.cached {
		fileIdx := uint8(i)
		c.cache.forEach(func(offset int64, data []byte) {
			buf = append(buf, fileIdx)
			buf = binary.LittleEndian.AppendUint64(buf, uint64(offset))
			buf = binary.LittleEndian.AppendUint32(buf, uint32(len(data)))
			buf = append(buf, data...)
		})
	}

	// Add bestHash entry for metaFile.
	buf = append(buf, metaFileIdx)
	buf = binary.LittleEndian.AppendUint64(buf, bestHashOffset)
	buf = binary.LittleEndian.AppendUint32(buf, 32)
	buf = append(buf, bestHash[:]...)

	return buf
}

// applyFromCaches writes cached entries directly to underlying files,
// avoiding intermediate allocations. Includes the bestHash entry.
func (w *WAL) applyFromCaches(bestHash [32]byte) error {
	for i, c := range w.cached {
		var applyErr error
		c.cache.forEach(func(offset int64, data []byte) {
			if applyErr != nil {
				return
			}
			if _, err := c.underlying.Seek(offset, io.SeekStart); err != nil {
				applyErr = fmt.Errorf("file %d seek to %d: %w", i, offset, err)
				return
			}
			if _, err := c.underlying.Write(data); err != nil {
				applyErr = fmt.Errorf("file %d write at %d: %w", i, offset, err)
				return
			}
		})
		if applyErr != nil {
			return applyErr
		}
	}

	// Write bestHash to metaFile at bestHashOffset.
	metaFile := w.cached[metaFileIdx].underlying
	if _, err := metaFile.Seek(bestHashOffset, io.SeekStart); err != nil {
		return fmt.Errorf("metaFile seek: %w", err)
	}
	if _, err := metaFile.Write(bestHash[:]); err != nil {
		return fmt.Errorf("metaFile write bestHash: %w", err)
	}

	return nil
}

// Discard drops all pending writes without committing.
func (w *WAL) Discard() {
	for _, c := range w.cached {
		c.Discard()
	}
}

// FlushNeeded returns true if any cached file has exceeded its memory threshold.
func (w *WAL) FlushNeeded() bool {
	for _, c := range w.cached {
		if c.FlushNeeded() {
			return true
		}
	}
	return false
}

// parseEntries decodes journal entries from a byte slice.
func parseEntries(buf []byte) ([]journalEntry, error) {
	var entries []journalEntry
	for len(buf) >= entryHeaderSize {
		fileIdx := buf[0]
		offset := int64(binary.LittleEndian.Uint64(buf[1:9]))
		dataLen := binary.LittleEndian.Uint32(buf[9:entryHeaderSize])
		buf = buf[entryHeaderSize:]

		if uint32(len(buf)) < dataLen {
			return nil, fmt.Errorf("wal: truncated entry data: need %d, have %d", dataLen, len(buf))
		}

		data := make([]byte, dataLen)
		copy(data, buf[:dataLen])
		buf = buf[dataLen:]

		entries = append(entries, journalEntry{
			fileIdx: fileIdx,
			offset:  offset,
			data:    data,
		})
	}
	if len(buf) != 0 {
		return nil, fmt.Errorf("wal: %d trailing bytes after last entry", len(buf))
	}
	return entries, nil
}

// applyEntries writes each entry to the appropriate underlying file.
func applyEntries(entries []journalEntry, underlying []ForestFile) error {
	for _, e := range entries {
		if int(e.fileIdx) >= len(underlying) {
			return fmt.Errorf("wal: fileIdx %d out of range (have %d files)", e.fileIdx, len(underlying))
		}
		f := underlying[e.fileIdx]
		if _, err := f.Seek(e.offset, io.SeekStart); err != nil {
			return err
		}
		if _, err := f.Write(e.data); err != nil {
			return err
		}
	}
	return nil
}

// clearJournal writes a zero totalLen to indicate no pending transaction
// and truncates the file to reclaim disk space.
func (w *WAL) clearJournal() error {
	if _, err := w.journal.Seek(0, io.SeekStart); err != nil {
		return err
	}
	var zero [journalHeaderSize]byte
	if _, err := w.journal.Write(zero[:]); err != nil {
		return err
	}
	// Truncate to reclaim disk space if the file supports it.
	if truncater, ok := w.journal.(interface{ Truncate(size int64) error }); ok {
		if err := truncater.Truncate(journalHeaderSize); err != nil {
			return err
		}
	}
	return syncFile(w.journal)
}

// recoverFromJournal replays any committed journal entries to the
// underlying files. Called once during NewWAL, before cachedRWS creation.
func (w *WAL) recoverFromJournal(underlying []ForestFile) error {
	// Get journal size.
	size, err := w.journal.Seek(0, io.SeekEnd)
	if err != nil {
		return err
	}

	if size < int64(journalMinSize) {
		return nil // No valid journal.
	}

	// Read totalLen.
	if _, err := w.journal.Seek(0, io.SeekStart); err != nil {
		return err
	}
	var totalLen uint64
	if err := binary.Read(w.journal, binary.LittleEndian, &totalLen); err != nil {
		return nil // Can't read header, nothing to recover.
	}

	if totalLen == 0 {
		return nil // No pending transaction.
	}

	// Bound totalLen to the file size and int64 limits to avoid overflow/OOM.
	if totalLen > uint64(size)-journalMinSize {
		return w.clearJournal()
	}
	if totalLen > ^uint64(0)>>1 { // max int64
		return w.clearJournal()
	}

	// Check if the full record fits in the file.
	recordSize := int64(journalHeaderSize) + int64(journalHashSize) + int64(totalLen) + int64(journalChecksumSize)
	if recordSize > size {
		// Incomplete write; underlying files have the old consistent state.
		return w.clearJournal()
	}

	// Read bestHash.
	var bestHash [journalHashSize]byte
	if _, err := io.ReadFull(w.journal, bestHash[:]); err != nil {
		return w.clearJournal()
	}

	// Read entries.
	entriesBuf := make([]byte, totalLen)
	if _, err := io.ReadFull(w.journal, entriesBuf); err != nil {
		return w.clearJournal()
	}

	// Read stored checksum.
	var storedChecksum uint32
	if err := binary.Read(w.journal, binary.LittleEndian, &storedChecksum); err != nil {
		return w.clearJournal()
	}

	// Verify CRC32 over header + bestHash + entries.
	crc := crc32.NewIEEE()
	var header [journalHeaderSize]byte
	binary.LittleEndian.PutUint64(header[:], totalLen)
	crc.Write(header[:])
	crc.Write(bestHash[:])
	crc.Write(entriesBuf)

	if crc.Sum32() != storedChecksum {
		// Corrupt journal; discard.
		return w.clearJournal()
	}

	// Parse and replay entries.
	entries, err := parseEntries(entriesBuf)
	if err != nil {
		return w.clearJournal()
	}

	if err := applyEntries(entries, underlying); err != nil {
		return err
	}

	// Sync underlying files after replay.
	for _, u := range underlying {
		if err := syncFile(u); err != nil {
			return err
		}
	}

	return w.clearJournal()
}

// syncFile calls Sync() on f if it supports it (e.g. *os.File).
// For implementations without Sync (e.g. memFile), this is a no-op.
func syncFile(f io.ReadWriteSeeker) error {
	if syncer, ok := f.(interface{ Sync() error }); ok {
		return syncer.Sync()
	}
	return nil
}
