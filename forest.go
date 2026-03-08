package utreexo

import (
	"encoding/binary"
	"fmt"
	"io"
	"math/bits"
	"os"
	"path/filepath"
	"sync"

	"github.com/utreexo/utreexo/internal/swisstable"
	"golang.org/x/exp/slices"
)

const (
	// defaultForestRows is the tree height used by OpenForest.
	// With forestRows=63 the position arithmetic works via unsigned
	// wrapping; the compact file layout (posToFileOffset) maps tree
	// positions to dense row-based offsets so file offsets stay within
	// int64 range.
	defaultForestRows = 63

	// maxFileLeavesBits caps the per-row slot count used by the
	// compact file layout.  Row r gets 1<<(maxFileLeavesBits-r) slots
	// (min 1).  With 34 this supports up to ~17 billion leaves while
	// keeping the sparse data file around 1 TB apparent size.
	maxFileLeavesBits = 34

	// File names used by OpenForest within the dbpath directory.
	forestDataFileName        = "forest_data.dat"         // main hash data, 32 bytes per position
	forestDeletedFileName     = "forest_deleted.dat"      // deleted-leaf bitmap, 8 bytes per word
	forestAddIndexFileName    = "forest_addindex.dat"     // add-batch index per leaf, 4 bytes each
	forestJournalFileName     = "forest_journal.dat"      // WAL journal for crash recovery
	forestMetaFileName        = "forest_meta.dat"         // recordMode + consistency hash
	forestPosMapCtrlFileName  = "forest_posmap_ctrl.dat"  // Swiss Table control bytes, mmap'd
	forestPosMapSlotsFileName = "forest_posmap_slots.dat" // Swiss Table slot values, mmap'd
)

// rowBaseOffset returns the byte offset where row r begins in the data
// file.  Rows 0..capBits each have 1<<(capBits-r) slots of 32 bytes
// (a geometric series).  row must be <= capBits.
func rowBaseOffset(row, forestRows uint8) int64 {
	capBits := min(forestRows, maxFileLeavesBits)
	return (int64(1)<<(capBits+1) - int64(1)<<(capBits-row+1)) * 32
}

// dataFileSize returns the total byte size of the compact data file
// for the given forestRows.  Rows 0..capBits follow the geometric
// series; rows capBits+1..63 each have a single 32-byte slot.
func dataFileSize(forestRows uint8) int64 {
	capBits := min(forestRows, maxFileLeavesBits)
	return (int64(1)<<(capBits+1) - 1 + int64(63-capBits)) * 32
}

// Assert that Forest implements the Utreexo interface.
var _ Utreexo = (*Forest)(nil)

// forestFile is the interface required for the main data file.
type forestFile interface {
	io.ReadWriteSeeker
	io.ReaderAt
}

// positionMap value packing: upper 17 bits = addIndex, lower 47 bits = position
// Supports up to 2^47 (~140 trillion) leaves and 2^17 (131,072) adds per block.
const (
	positionBits = 47
	positionMask = (1 << positionBits) - 1
)

func packPosIndex(pos uint64, addIndex int32) uint64 {
	return (uint64(uint32(addIndex)) << positionBits) | (pos & positionMask)
}

func unpackPos(v uint64) uint64  { return v & positionMask }
func unpackIndex(v uint64) int32 { return int32(v >> positionBits) }

// deletedBitmap tracks deleted leaf positions using 1 bit per position.
// Position N is stored at bit (N % 64) of bits[N / 64].
// This is more memory-efficient and cache-friendly than a map.
//
// dirtyWords tracks which bitmap words have been modified since the last
// flush/clear. The WAL uses this to serialize only changed words.
type deletedBitmap struct {
	bits       []uint64
	dirtyWords map[uint64]struct{}
}

// newDeletedBitmap creates a bitmap sized to track numLeaves positions.
func newDeletedBitmap(numLeaves uint64) *deletedBitmap {
	numWords := (numLeaves + 63) / 64
	return &deletedBitmap{
		bits:       make([]uint64, numWords),
		dirtyWords: make(map[uint64]struct{}),
	}
}

// set marks the given position as deleted. Grows the bitmap if needed.
func (b *deletedBitmap) set(pos uint64) {
	word := pos / 64
	if word >= uint64(len(b.bits)) {
		newBits := make([]uint64, word+1)
		copy(newBits, b.bits)
		b.bits = newBits
	}
	b.bits[word] |= 1 << (pos % 64)
	b.dirtyWords[word] = struct{}{}
}

// unset marks the given position as not deleted.
func (b *deletedBitmap) unset(pos uint64) {
	word := pos / 64
	if word >= uint64(len(b.bits)) {
		return
	}
	b.bits[word] &^= 1 << (pos % 64)
	b.dirtyWords[word] = struct{}{}
}

// forEachDirty calls fn for each dirty bitmap word, providing the byte offset
// in the file and the 8-byte little-endian encoded word.
func (b *deletedBitmap) forEachDirty(fn func(offset int64, data []byte)) {
	for wordIdx := range b.dirtyWords {
		// This should never happen in practice since dirtyWords are only
		// added by set/unset which ensure the index is within bounds.
		if wordIdx >= uint64(len(b.bits)) {
			continue
		}
		var buf [8]byte
		binary.LittleEndian.PutUint64(buf[:], b.bits[wordIdx])
		fn(int64(wordIdx)*8, buf[:])
	}
}

// clearDirty resets dirty tracking. Called after WAL flush or discard.
func (b *deletedBitmap) clearDirty() {
	clear(b.dirtyWords)
}

// loadDeletedBitmap reads a bitmap file into a new deletedBitmap.
// The file stores uint64 words in little-endian format, one per 8 bytes.
func loadDeletedBitmap(file io.ReadSeeker) (*deletedBitmap, error) {
	size, err := file.Seek(0, io.SeekEnd)
	if err != nil {
		return nil, err
	}

	if size == 0 {
		return newDeletedBitmap(0), nil
	}

	if size%8 != 0 {
		return nil, fmt.Errorf("bitmap file size %d is not a multiple of 8", size)
	}

	if _, err := file.Seek(0, io.SeekStart); err != nil {
		return nil, err
	}

	buf := make([]byte, size)
	if _, err := io.ReadFull(file, buf); err != nil {
		return nil, err
	}

	numWords := uint64(size) / 8
	// Multiply by 64 to convert from word count to a capacity that
	// newDeletedBitmap will round back into the correct word count.
	b := newDeletedBitmap(numWords * 64)
	for i := range numWords {
		b.bits[i] = binary.LittleEndian.Uint64(buf[i*8:])
	}

	return b, nil
}

// isSet returns true if the given position is marked as deleted.
func (b *deletedBitmap) isSet(pos uint64) bool {
	word := pos / 64
	if word >= uint64(len(b.bits)) {
		return false
	}
	return b.bits[word]&(1<<(pos%64)) != 0
}

// count returns the total number of deleted positions.
func (b *deletedBitmap) count() int {
	n := 0
	for _, word := range b.bits {
		n += bits.OnesCount64(word)
	}
	return n
}

// Forest is a Utreexo accumulator backed by a contiguous file.
// Nodes are stored at row-based offsets computed by posToFileOffset:
// each row gets a dense section sized by maxFileLeavesBits so that
// even with forestRows=63 file offsets stay within int64 range.
// Deleted leaves remain in the file for Undo support.
//
// Unlike Pollard which uses pointer-based trees, Forest stores everything
// in a flat file. Deletions work by copying the sibling hash to the
// parent position.
//
// Forest uses a fixed forestRows to ensure stable position mappings.
// This is set at creation time based on expected maximum leaves.
type Forest struct {
	mu sync.RWMutex // protects all fields below

	file         forestFile
	addIndexFile forestFile // stores int32 addIndex at offset pos*4
	metaFile     forestFile // stores recordMode (bytes 0-31) + consistency hash (bytes 32-63)
	NumLeaves    uint64
	forestRows   uint8 // Fixed maximum rows for stable position mapping

	// positionMap maps leaf hashes to packed (addIndex, position) values.
	// Upper 17 bits = addIndex (index within Modify batch), lower 47 bits = position.
	// Only tracks leaves (row 0), not intermediate nodes.
	// Uses Swiss Table with mmap'd files for memory efficiency.
	positionMap *swisstable.SwissPositionMap

	// deletedLeafPositions tracks which leaf positions have been deleted.
	// Persisted via the WAL (dirty words are serialized during flush).
	// On restart the bitmap is loaded from the underlying file by the WAL
	// (or loadDeletedBitmap for non-WAL usage) and passed to newForest.
	deletedLeafPositions *deletedBitmap

	// recordMode is true after Record is called but before HashAll completes.
	// Calling Modify while in record mode would corrupt the tree.
	// Persisted to metaFile (bytes 0-31, padded).
	recordMode bool

	// wal is set when created via OpenForest; nil for newForest (test/advanced usage).
	wal *wal

	// closers holds os.File handles to close on Close(). Only set by OpenForest.
	closers []io.Closer
}

// newForest creates a new Forest backed by the given file.
// The file should be an io.ReadWriteSeeker (e.g., *os.File).
// addIndexFile stores the addIndex for each leaf; its size determines numLeaves (size / 4).
// metaFile stores recordMode (bytes 0-31) and consistency hash (bytes 32-63).
// bitmap tracks deleted leaf positions; pass nil for a fresh forest. When using a WAL,
// the bitmap is loaded by the WAL after recovery and passed here. For non-WAL usage,
// load it with loadDeletedBitmap.
// posMapCtrlPath and posMapSlotsPath are file paths for the Swiss Table position map.
// forestRows sets the maximum tree height (determines max leaves = 2^forestRows).
func newForest(file forestFile, addIndexFile, metaFile forestFile, bitmap *deletedBitmap, posMapCtrlPath, posMapSlotsPath string, forestRows uint8) (*Forest, error) {
	if file == nil || addIndexFile == nil || metaFile == nil {
		return nil, fmt.Errorf("one of the given files are nil")
	}

	// Derive numLeaves from addIndexFile size (each leaf stores a 4-byte int32).
	addIdxSize, err := addIndexFile.Seek(0, io.SeekEnd)
	if err != nil {
		return nil, fmt.Errorf("get addIndexFile size: %w", err)
	}
	numLeaves := uint64(addIdxSize / 4)

	// Read consistency hash from metaFile (bytes 32-63, written atomically by WAL).
	// Zero hash on first run or if metaFile is empty.
	var consistencyHash [32]byte
	metaFile.Seek(32, io.SeekStart)
	metaFile.Read(consistencyHash[:])

	// Create Swiss Table for position map. Size based on numLeaves (will resize if needed).
	// Use a minimum of 1<<16 to avoid excessive early resizes on a fresh database.
	expectedEntries := max(numLeaves, 1<<16)
	posMap, needsRebuild, err := swisstable.NewSwissPositionMap(posMapCtrlPath, posMapSlotsPath, expectedEntries, consistencyHash, file, positionMask)
	if err != nil {
		return nil, fmt.Errorf("create position map: %w", err)
	}

	if bitmap == nil {
		bitmap = newDeletedBitmap(numLeaves)
	}

	f := &Forest{
		file:                 file,
		addIndexFile:         addIndexFile,
		metaFile:             metaFile,
		NumLeaves:            numLeaves,
		forestRows:           forestRows,
		positionMap:          posMap,
		deletedLeafPositions: bitmap,
	}

	// Load metadata (recordMode)
	if err := f.loadMetadata(); err != nil {
		return nil, fmt.Errorf("load metadata: %w", err)
	}

	// Rebuild positionMap only if needed (new file or hash mismatch)
	if needsRebuild {
		if err := f.rebuildPositionMap(); err != nil {
			return nil, fmt.Errorf("rebuild positionMap: %w", err)
		}
	}

	return f, nil
}

// ForestOption configures OpenForest behavior.
type ForestOption func(*forestOptions)

type forestOptions struct {
	maxCacheMemory int64
}

// MaxCacheMemory sets the total WAL cache memory budget in bytes.
// The budget is split proportionally across files by entry size.
// If zero or not set, each file uses the WAL default (64MB).
func MaxCacheMemory(bytes int64) ForestOption {
	return func(o *forestOptions) {
		o.maxCacheMemory = bytes
	}
}

// OpenForest opens a file-backed Forest at the given directory path,
// creating it if it doesn't exist. It sets up a WAL with default cache
// sizes and wires up the OnFlush callback for position map syncing.
//
// Use Close() to flush pending data and release file handles.
// For custom cache sizes or in-memory usage within the package/tests, use newForest.
func OpenForest(dbpath string, opts ...ForestOption) (*Forest, error) {
	var o forestOptions
	for _, opt := range opts {
		opt(&o)
	}

	if err := os.MkdirAll(dbpath, 0700); err != nil {
		return nil, fmt.Errorf("create dbpath: %w", err)
	}

	fileNames := []string{
		forestDataFileName,
		forestDeletedFileName,
		forestAddIndexFileName,
		forestJournalFileName,
		forestMetaFileName,
	}

	files := make([]*os.File, 0, len(fileNames))
	for _, name := range fileNames {
		f, err := os.OpenFile(filepath.Join(dbpath, name), os.O_RDWR|os.O_CREATE, 0600)
		if err != nil {
			for _, prev := range files {
				prev.Close()
			}
			return nil, fmt.Errorf("open %s: %w", name, err)
		}
		files = append(files, f)
	}

	dataFile, deletedFile, addIndexFile, journalFile, metaFile := files[0], files[1], files[2], files[3], files[4]
	closers := make([]io.Closer, len(files))
	for i, f := range files {
		closers[i] = f
	}

	// Ensure the data file spans the full compact row layout before the
	// WAL wraps it, so the cachedRWS layer sees the correct file size.
	// On filesystems with sparse-file support only written blocks
	// consume physical disk space.
	totalSize := dataFileSize(defaultForestRows)
	if err := dataFile.Truncate(totalSize); err != nil {
		for _, c := range closers {
			c.Close()
		}
		return nil, fmt.Errorf("truncate data file: %w", err)
	}

	// Split memory budget proportionally by entry size so caches fill
	// at similar rates. Entry sizes: data=32, addIndex=4, meta=32.
	// When maxCacheMemory is 0 each walFile gets the WAL default (64MB).
	const (
		dataEntrySize     = 32
		addIndexEntrySize = 4
		metaEntrySize     = 32
		totalEntrySize    = dataEntrySize + addIndexEntrySize // meta is tiny, use WAL default
	)
	var dataCacheBytes, addIndexCacheBytes int64
	if o.maxCacheMemory > 0 {
		dataCacheBytes = o.maxCacheMemory * dataEntrySize / totalEntrySize
		addIndexCacheBytes = o.maxCacheMemory * addIndexEntrySize / totalEntrySize
	}

	wal, err := newWAL(journalFile, deletedFile,
		walFile{File: dataFile, EntrySize: dataEntrySize, MaxCacheBytes: dataCacheBytes},
		walFile{File: addIndexFile, EntrySize: addIndexEntrySize, MaxCacheBytes: addIndexCacheBytes},
		walFile{File: metaFile, EntrySize: metaEntrySize},
	)
	if err != nil {
		for _, c := range closers {
			c.Close()
		}
		return nil, fmt.Errorf("create wal: %w", err)
	}

	ctrlPath := filepath.Join(dbpath, forestPosMapCtrlFileName)
	slotsPath := filepath.Join(dbpath, forestPosMapSlotsFileName)

	f, err := newForest(
		wal.Cached(0), wal.Cached(1), wal.Cached(2),
		wal.Bitmap(),
		ctrlPath, slotsPath,
		defaultForestRows,
	)
	if err != nil {
		for _, c := range closers {
			c.Close()
		}
		return nil, fmt.Errorf("create forest: %w", err)
	}

	wal.SetOnFlush(func(hash [32]byte) error {
		return f.SyncPositionMap(hash)
	})

	f.wal = wal
	f.closers = closers

	return f, nil
}

// Flush atomically commits all cached writes through the WAL journal.
// Only valid on forests created via OpenForest.
func (f *Forest) Flush(bestHash [32]byte) error {
	if f.wal == nil {
		return fmt.Errorf("flush: no WAL (use OpenForest to enable)")
	}
	return f.wal.Flush(bestHash)
}

// FlushNeeded returns true if any cached file has exceeded its memory threshold.
// Always returns false for forests without a WAL.
func (f *Forest) FlushNeeded() bool {
	if f.wal == nil {
		return false
	}
	return f.wal.FlushNeeded()
}

// Close flushes pending writes and closes the position map and all
// underlying file handles. bestHash is the consistency hash written
// to the WAL during the final flush.
func (f *Forest) Close(bestHash [32]byte) error {
	var firstErr error
	if f.wal != nil {
		if err := f.wal.Flush(bestHash); err != nil {
			firstErr = err
		}
	}
	if err := f.positionMap.Close(); err != nil && firstErr == nil {
		firstErr = err
	}
	for _, c := range f.closers {
		if err := c.Close(); err != nil && firstErr == nil {
			firstErr = err
		}
	}
	f.closers = nil
	return firstErr
}

// rebuildPositionMap reads all leaf hashes and addIndices in parallel bulk reads
// and populates the positionMap, skipping deleted positions.
func (f *Forest) rebuildPositionMap() error {
	if f.NumLeaves == 0 {
		return nil
	}

	const batchSize = 4096 // entries per batch
	type batch struct {
		pos  uint64
		size uint64
		data []byte
	}

	// done is closed on any error to signal producer goroutines to exit.
	done := make(chan struct{})
	defer close(done)

	// readBatches reads fixed-size entries from r in batches, sending them on
	// ch. It closes ch when finished and respects done for early cancellation.
	readBatches := func(r io.ReadWriteSeeker, entrySize uint64, ch chan<- batch) error {
		defer close(ch)

		if _, err := r.Seek(0, io.SeekStart); err != nil {
			return err
		}

		for pos := uint64(0); pos < f.NumLeaves; pos += batchSize {
			n := min(uint64(batchSize), f.NumLeaves-pos)

			buf := make([]byte, n*entrySize)
			if _, err := io.ReadFull(r, buf); err != nil {
				return err
			}

			select {
			case ch <- batch{pos: pos, size: n, data: buf}:
			case <-done:
				return nil
			}
		}
		return nil
	}

	hashCh := make(chan batch, 4)
	addIdxCh := make(chan batch, 4)
	hashErrCh := make(chan error, 1)
	addIdxErrCh := make(chan error, 1)

	go func() { hashErrCh <- readBatches(f.file, 32, hashCh) }()
	go func() { addIdxErrCh <- readBatches(f.addIndexFile, 4, addIdxCh) }()

	// Consumer: process batches as they arrive.
	for hashBatch := range hashCh {
		addIdxBatch, ok := <-addIdxCh
		if !ok {
			if err := <-addIdxErrCh; err != nil {
				return fmt.Errorf("read addIndex: %w", err)
			}
			return fmt.Errorf("addIdx channel closed early")
		}
		if hashBatch.pos != addIdxBatch.pos || hashBatch.size != addIdxBatch.size {
			return fmt.Errorf("batch mismatch: hash pos=%d size=%d, addIdx pos=%d size=%d",
				hashBatch.pos, hashBatch.size, addIdxBatch.pos, addIdxBatch.size)
		}

		for i := uint64(0); i < hashBatch.size; i++ {
			leafPos := hashBatch.pos + i

			var hash Hash
			copy(hash[:], hashBatch.data[i*32:])

			addIndex := int32(binary.LittleEndian.Uint32(addIdxBatch.data[i*4:]))
			if err := f.positionMap.Set(hash, packPosIndex(leafPos, addIndex)); err != nil {
				return fmt.Errorf("positionMap.Set at %d: %w", leafPos, err)
			}
		}
	}

	// hashCh is closed — check the hash reader for errors.
	if err := <-hashErrCh; err != nil {
		return fmt.Errorf("read hashes: %w", err)
	}

	// Drain any remaining addIdx batches and check for errors.
	for range addIdxCh {
	}
	if err := <-addIdxErrCh; err != nil {
		return fmt.Errorf("read addIndex: %w", err)
	}

	return nil
}

// loadMetadata reads recordMode from metaFile (bytes 0-31, padded).
func (f *Forest) loadMetadata() error {
	_, err := f.metaFile.Seek(0, io.SeekStart)
	if err != nil {
		return err
	}
	var buf [32]byte
	n, err := f.metaFile.Read(buf[:])
	if err != nil && err != io.EOF {
		return err
	}
	if n >= 1 {
		f.recordMode = buf[0] != 0
	}
	return nil
}

// saveRecordMode writes the recordMode to metaFile (bytes 0-31, padded).
func (f *Forest) saveRecordMode() error {
	_, err := f.metaFile.Seek(0, io.SeekStart)
	if err != nil {
		return err
	}

	var buf [32]byte
	if f.recordMode {
		buf[0] = 1
	}
	_, err = f.metaFile.Write(buf[:])
	return err
}

// ReadConsistencyHash reads the consistency hash from metaFile (bytes 32-63).
// The hash is written atomically by WAL.Flush().
func (f *Forest) ReadConsistencyHash() ([32]byte, error) {
	var hash [32]byte
	_, err := f.metaFile.Seek(32, io.SeekStart)
	if err != nil {
		return hash, err
	}
	_, err = io.ReadFull(f.metaFile, hash[:])
	return hash, err
}

// GetNumLeaves returns the total number of leaves added to the forest.
//
// This function is safe for concurrent access.
func (f *Forest) GetNumLeaves() uint64 {
	f.mu.RLock()
	defer f.mu.RUnlock()
	return f.NumLeaves
}

// GetTreeRows returns the fixed number of rows in the forest.
//
// This function is safe for concurrent access.
func (f *Forest) GetTreeRows() uint8 {
	f.mu.RLock()
	defer f.mu.RUnlock()
	return TreeRows(f.NumLeaves)
}

// SyncPositionMap updates the stored consistency hash in the position map.
// It first fsyncs the mmap'd ctrl and slots files to make all pending position
// map writes durable, then writes the consistency hash into both file headers
// and fsyncs again. Call this after WAL flush succeeds to enable skipping
// rebuild on restart.
func (f *Forest) SyncPositionMap(consistencyHash [32]byte) error {
	return f.positionMap.SetConsistencyHash(consistencyHash)
}

// posToFileOffset translates a tree position to a byte offset in the
// data file.  Each row is stored in a dense section whose start is
// precomputed in rowBase; the offset within the row is the distance
// from the row's first position.
func (f *Forest) posToFileOffset(position uint64) int64 {
	row := DetectRow(position, f.forestRows)
	rowStart := startPositionAtRow(row, f.forestRows)
	return rowBaseOffset(row, f.forestRows) + int64(position-rowStart)*32
}

// readHash reads the hash at the given position from the file.
func (f *Forest) readHash(position uint64) (Hash, error) {
	offset := f.posToFileOffset(position)
	_, err := f.file.Seek(offset, io.SeekStart)
	if err != nil {
		return Hash{}, fmt.Errorf("seek to position %d: %w", position, err)
	}

	var hash Hash
	n, err := f.file.Read(hash[:])
	if err != nil {
		return Hash{}, fmt.Errorf("read at position %d: %w", position, err)
	}
	if n != 32 {
		return Hash{}, fmt.Errorf("short read at position %d: got %d bytes", position, n)
	}

	return hash, nil
}

// writeHash writes the hash at the given position to the file.
func (f *Forest) writeHash(position uint64, hash Hash) error {
	offset := f.posToFileOffset(position)
	_, err := f.file.Seek(offset, io.SeekStart)
	if err != nil {
		return fmt.Errorf("seek to position %d: %w", position, err)
	}

	n, err := f.file.Write(hash[:])
	if err != nil {
		return fmt.Errorf("write at position %d: %w", position, err)
	}
	if n != 32 {
		return fmt.Errorf("short write at position %d: wrote %d bytes", position, n)
	}

	return nil
}

// readAddIndex reads the addIndex for the leaf at the given position.
func (f *Forest) readAddIndex(pos uint64) (int32, error) {
	offset := int64(pos * 4)
	_, err := f.addIndexFile.Seek(offset, io.SeekStart)
	if err != nil {
		return 0, err
	}

	var addIndex int32
	err = binary.Read(f.addIndexFile, binary.LittleEndian, &addIndex)
	if err != nil {
		return 0, err
	}

	return addIndex, nil
}

// writeAddIndex writes the addIndex for the leaf at the given position.
func (f *Forest) writeAddIndex(pos uint64, addIndex int32) error {
	offset := int64(pos * 4)
	_, err := f.addIndexFile.Seek(offset, io.SeekStart)
	if err != nil {
		return err
	}

	return binary.Write(f.addIndexFile, binary.LittleEndian, addIndex)
}

// add adds a single leaf to the forest.
// If hash is empty, the sibling (existing root) moves up to the parent position.
func (f *Forest) add(hash Hash, addIndex int32) error {
	// Add to position map (before incrementing NumLeaves)
	if hash != empty {
		if err := f.positionMap.Set(hash, packPosIndex(f.NumLeaves, addIndex)); err != nil {
			return fmt.Errorf("positionMap.Set: %w", err)
		}

		// Write the leaf hash at position NumLeaves
		err := f.writeHash(f.NumLeaves, hash)
		if err != nil {
			return fmt.Errorf("write leaf: %w", err)
		}

		// Write the addIndex
		err = f.writeAddIndex(f.NumLeaves, addIndex)
		if err != nil {
			return fmt.Errorf("write addIndex: %w", err)
		}
	}

	currentHash := hash
	currentPos := f.NumLeaves

	// Hash with existing roots based on binary representation of NumLeaves.
	// Wherever there's a 1 bit, there's an existing root to hash with.
	for h := uint8(0); (f.NumLeaves>>h)&1 == 1; h++ {
		// Get the existing root position at row h
		rootPos := rootPosition(f.NumLeaves, h, f.forestRows)

		// Read the existing root hash
		rootHash, err := f.readHash(rootPos)
		if err != nil {
			return fmt.Errorf("read root at row %d: %w", h, err)
		}

		// Check if this root is a deleted leaf - treat as empty if so
		if f.deletedLeafPositions.isSet(rootPos) {
			rootHash = empty
		}

		// Calculate parent position
		parentPos := Parent(currentPos, f.forestRows)

		// Handle empty hashes using parentHash logic
		newHash := parentHash(rootHash, currentHash)

		// Write the parent hash
		err = f.writeHash(parentPos, newHash)
		if err != nil {
			return fmt.Errorf("write parent at position %d: %w", parentPos, err)
		}

		currentHash = newHash
		currentPos = parentPos
	}

	f.NumLeaves++
	return nil
}

func (f *Forest) delete(delHashes []Hash) error {
	if len(delHashes) == 0 {
		return nil
	}

	for _, delHash := range delHashes {
		_, found, err := f.positionMap.Get(delHash)
		if err != nil {
			return fmt.Errorf("positionMap.Get: %w", err)
		}
		if !found {
			return fmt.Errorf("delhash %v not found in position map", delHash)
		}
	}

	for _, delHash := range delHashes {
		err := f.deleteSingle(delHash)
		if err != nil {
			return err
		}
	}

	return nil
}

func (f *Forest) deleteSingle(delHash Hash) error {
	// Get the packed value (contains position + addIndex)
	packed, _, err := f.positionMap.Get(delHash)
	if err != nil {
		return fmt.Errorf("positionMap.Get: %w", err)
	}
	leafPos := unpackPos(packed)

	// Mark position as deleted in the in-memory bitmap.
	// The WAL will persist dirty bitmap words during flush.
	f.deletedLeafPositions.set(leafPos)

	// First I need to check if I moved up.
	pos := leafPos
	parentPos := Parent(pos, f.forestRows)
	pHash, err := f.readHash(parentPos)
	if err != nil {
		return err
	}

	for pHash == delHash {
		pos = parentPos
		parentPos = Parent(pos, f.forestRows)
		pHash, err = f.readHash(parentPos)
		if err != nil {
			return err
		}
	}

	if isRootPositionTotalRows(pos, f.NumLeaves, f.forestRows) {
		row := DetectRow(pos, f.forestRows)
		if row == 0 {
			// Don't overwrite - just mark as deleted (already done above).
			// The hash is preserved for undo. GetRoots will return empty for deleted roots.
		} else {
			err = f.writeHash(pos, empty)
			if err != nil {
				return err
			}
		}
		return nil
	}

	sibPos := sibling(pos)
	sibHash, err := f.readHash(sibPos)
	if err != nil {
		return err
	}

	// Then I write my hash.
	err = f.writeHash(parentPos, sibHash)
	if err != nil {
		return err
	}
	sibHashPos := parentPos // track where sibHash is written

	// After that, I need to check if my parents moved up.
	parentPos = Parent(parentPos, f.forestRows)
	curHash := pHash
	pHash, err = f.readHash(parentPos)
	if err != nil {
		return err
	}

	for curHash == pHash {
		err = f.writeHash(parentPos, sibHash)
		if err != nil {
			return err
		}
		sibHashPos = parentPos // update position where sibHash lives
		parentPos = Parent(parentPos, f.forestRows)
		pHash, err = f.readHash(parentPos)
		if err != nil {
			return err
		}
	}

	err = f.rehashToRoot(sibHashPos, sibHash)
	if err != nil {
		return err
	}

	return nil
}

// rehashToRoot rehashes from the given position up to the root.
// The hash at pos is provided to avoid an extra read.
func (f *Forest) rehashToRoot(pos uint64, hash Hash) error {
	currentHash := hash
	// Track the original hash at our position (before any writes).
	// This is used to detect if sibling was deleted: if parent == originalPosHash,
	// it means our old hash moved up when sibling was deleted.
	originalPosHash := hash

	for !isRootPositionTotalRows(pos, f.NumLeaves, f.forestRows) {
		parentPos := Parent(pos, f.forestRows)
		parentH, err := f.readHash(parentPos)
		if err != nil {
			return fmt.Errorf("read parent at %d: %w", parentPos, err)
		}

		// Check if sibling was deleted: if parent contains our original hash,
		// it means our hash moved up when sibling was deleted.
		// We should just propagate currentHash up (continue the move-up).
		if parentH == originalPosHash {
			err = f.writeHash(parentPos, currentHash)
			if err != nil {
				return fmt.Errorf("write parent at %d: %w", parentPos, err)
			}
			// For next iteration: the original hash at parentPos was parentH (= originalPosHash)
			// Since we moved up, the chain continues
			originalPosHash = parentH
			pos = parentPos
			continue
		}

		sibPos := sibling(pos)
		sibHash, err := f.readHash(sibPos)
		if err != nil {
			return fmt.Errorf("read sibling at %d: %w", sibPos, err)
		}

		var newParentHash Hash
		if isLeftNiece(pos) {
			newParentHash = parentHash(currentHash, sibHash)
		} else {
			newParentHash = parentHash(sibHash, currentHash)
		}

		// Save the old parent hash before overwriting - we need it for next iteration's check
		oldParentH := parentH

		err = f.writeHash(parentPos, newParentHash)
		if err != nil {
			return fmt.Errorf("write parent at %d: %w", parentPos, err)
		}

		pos = parentPos
		currentHash = newParentHash
		originalPosHash = oldParentH // This was at pos before we wrote
	}

	return nil
}

// GetRoots returns the current root hashes of the forest.
// Implements the ToString interface.
//
// This function is safe for concurrent access.
func (f *Forest) GetRoots() []Hash {
	f.mu.RLock()
	defer f.mu.RUnlock()
	return f.getRoots()
}

// getRoots is the internal implementation of GetRoots.
//
// This function is NOT safe for concurrent access.
func (f *Forest) getRoots() []Hash {
	rootPositions := RootPositions(f.NumLeaves, f.forestRows)

	roots := make([]Hash, len(rootPositions))
	for i, pos := range rootPositions {
		// Check if this root position is a deleted leaf - return empty if so
		if f.deletedLeafPositions.isSet(pos) {
			roots[i] = empty
			continue
		}
		hash, err := f.readHash(pos)
		if err != nil {
			roots[i] = empty
		} else {
			roots[i] = hash
		}
	}

	return roots
}

// getHash returns the hash at the logical position of the forest.
//
// This function is NOT safe for concurrent access.
func (f *Forest) getHash(pos uint64) Hash {
	// Tree is the root the position is located under.
	// branchLen denotes how far down the root the position is.
	// bits tell us if we should go down to the left child or the right child.
	if pos >= maxPosition(TreeRows(f.NumLeaves)) {
		return empty
	}
	tree, branchLen, _, err := DetectOffset(pos, f.NumLeaves, TreeRows(f.NumLeaves))
	if err != nil {
		return empty
	}
	if tree >= numRoots(f.NumLeaves) {
		return empty
	}

	startPos := RootPositions(f.NumLeaves, f.forestRows)[tree]
	startHash, err := f.readHash(startPos)
	if err != nil {
		return empty
	}

	// If the root is empty, then everything else is empty.
	if startHash == empty {
		return empty
	}

	// If the root is at row 0, check if it's been deleted as the hash will not be empty.
	if DetectRow(startPos, f.forestRows) == 0 {
		if f.deletedLeafPositions.isSet(startPos) {
			return empty
		}

		// If the hash isn't empty we can just return here.
		return startHash
	}

	for h := int(branchLen) - 1; h >= 0; h-- {
		// If we're at this stage, that means we need to go down. But if the position is at row 0,
		// we can't go down any further.  This indicates that the position is already deleted.
		if DetectRow(startPos, f.forestRows) == 0 {
			return empty
		}

		lChildHash, err := f.readHash(LeftChild(startPos, f.forestRows))
		if err != nil {
			return empty
		}
		rChildHash, err := f.readHash(RightChild(startPos, f.forestRows))
		if err != nil {
			return empty
		}

		// Skip a branch if the hashes are the same. This means that the current root doesn't actually exist.
		switch startHash {
		case lChildHash:
			startPos = LeftChild(startPos, f.forestRows)
			startHash = lChildHash
			h++

			continue

		case rChildHash:
			startPos = RightChild(startPos, f.forestRows)
			startHash = rChildHash
			h++

			continue
		}

		// Figure out which node we need to follow.
		childPos := uint8(pos>>h) & 1
		if isLeftNiece(uint64(childPos)) {
			startPos = LeftChild(startPos, f.forestRows)
			startHash = lChildHash
		} else {
			startPos = RightChild(startPos, f.forestRows)
			startHash = rChildHash
		}
	}

	return startHash
}

// GetHash returns the hash at the given position in defaultForestRows space.
// Implements the ToString interface for debugging.
// Traverses from root to target position, following the tree structure
// and handling move-ups where a child's hash equals its parent's hash.
//
// This function is safe for concurrent access.
func (f *Forest) GetHash(position uint64) Hash {
	f.mu.RLock()
	defer f.mu.RUnlock()

	treeRows := TreeRows(f.NumLeaves)
	if treeRows != defaultForestRows {
		position = translatePos(position, defaultForestRows, treeRows)
	}
	return f.getHash(position)
}

// Undo reverts a modification done by Modify.
// This implements the Utreexo interface.
//
// This function is safe for concurrent access.
func (f *Forest) Undo(prevAdds []Hash, proof Proof, delHashes, prevRoots []Hash) error {
	f.mu.Lock()
	defer f.mu.Unlock()

	if f.recordMode {
		return fmt.Errorf("cannot call Undo while in record mode; call HashAll first")
	}

	return f.undoInternal(uint64(len(prevAdds)), delHashes)
}

// undoInternal reverts additions and deletions.
// numAdds is how many leaves were added in the block being undone.
// delHashes are the hashes that were deleted in the block being undone;
// their positions are looked up from positionMap.
func (f *Forest) undoInternal(numAdds uint64, delHashes []Hash) error {
	// Step 1: Undo additions - delete from positionMap before decrementing NumLeaves.
	for i := range numAdds {
		pos := f.NumLeaves - numAdds + i
		hash, err := f.readHash(pos)
		if err != nil {
			return fmt.Errorf("read hash at %d for undo add: %w", pos, err)
		}
		if _, err := f.positionMap.Delete(hash); err != nil {
			return fmt.Errorf("positionMap.Delete at %d: %w", pos, err)
		}
	}
	f.NumLeaves -= numAdds

	// Step 2: Look up deleted positions from positionMap
	delPositions := make([]uint64, len(delHashes))
	for i, hash := range delHashes {
		packed, found, err := f.positionMap.Get(hash)
		if err != nil {
			return fmt.Errorf("positionMap.Get for undo del: %w", err)
		}
		if !found {
			return fmt.Errorf("hash not found in positionMap for undo")
		}
		delPositions[i] = unpackPos(packed)
	}

	// Step 3: Undo deletions in reverse order (LIFO)
	for i := len(delPositions) - 1; i >= 0; i-- {
		pos := delPositions[i]
		f.deletedLeafPositions.unset(pos)

		err := f.undoSingleDeletion(pos)
		if err != nil {
			return err
		}
	}

	return nil
}

func (f *Forest) undoSingleDeletion(pos uint64) error {
	if isRootPositionTotalRows(pos, f.NumLeaves, f.forestRows) {
		return nil
	}

	// Undoing a single deletion is in 5 steps,
	//
	// 1: We grab the current position of the deleted hash as it may have moved up.
	// 2: We calculate the parent hash with the sibling (calculated from the current position).
	// 3: We insert the parent hash into the parent position.
	// 4: We check if the old hash in the parent position moved up as well, inserting theh parent hash
	//    whereever needed.
	// 5: From the last position we've inserted the parent hash (calculated in 3), we rehash to the root
	//    (while keeping in mind to move up hashes if the sibling is deleted).
	hash, err := f.readHash(pos)
	if err != nil {
		return err
	}

	parentPos := Parent(pos, f.forestRows)
	pHash, err := f.readHash(parentPos)
	if err != nil {
		return err
	}

	for pHash == hash {
		pos = parentPos
		parentPos = Parent(pos, f.forestRows)
		pHash, err = f.readHash(parentPos)
		if err != nil {
			return err
		}
	}

	// Check if we already wrote to the root.
	if isRootPositionTotalRows(parentPos, f.NumLeaves, f.forestRows) {
		pHash, err := f.readHash(parentPos)
		if err != nil {
			return err
		}

		// If the parent is a root and it's empty, that means my sib got deleted too.
		if pHash == empty {
			err = f.writeHash(parentPos, hash)
			return err
		}
	}

	sibPos := sibling(pos)
	sibHash, err := f.readHash(sibPos)
	if err != nil {
		return err
	}

	// Calculate parent hash (order depends on left/right)
	var newParentHash Hash
	if isLeftNiece(pos) {
		newParentHash = parentHash(hash, sibHash)
	} else {
		newParentHash = parentHash(sibHash, hash)
	}

	lastWritePos := parentPos
	prevHash := pHash

	err = f.writeHash(lastWritePos, newParentHash)
	if err != nil {
		return err
	}

	// Check if we already wrote to the root
	if isRootPositionTotalRows(lastWritePos, f.NumLeaves, f.forestRows) {
		return nil
	}

	parentPos = Parent(lastWritePos, f.forestRows)
	pHash, err = f.readHash(parentPos)
	if err != nil {
		return err
	}

	// Step 4: Check if the old hash in the parent position moved up as well
	for prevHash == pHash {
		err = f.writeHash(parentPos, newParentHash)
		if err != nil {
			return err
		}
		lastWritePos = parentPos

		if isRootPositionTotalRows(parentPos, f.NumLeaves, f.forestRows) {
			return nil
		}

		parentPos = Parent(parentPos, f.forestRows)
		pHash, err = f.readHash(parentPos)
		if err != nil {
			return err
		}
	}

	// Step 5: Rehash from the last write position to the root
	return f.rehashToRootFromPos(lastWritePos)
}

// rehashToRootFromPos recalculates hashes from the given position up to its root.
func (f *Forest) rehashToRootFromPos(pos uint64) error {
	currentPos := pos

	for !isRootPositionTotalRows(currentPos, f.NumLeaves, f.forestRows) {
		// Read current hash
		currentHash, err := f.readHash(currentPos)
		if err != nil {
			return fmt.Errorf("read current at %d: %w", currentPos, err)
		}

		parentPos := Parent(currentPos, f.forestRows)
		parentH, err := f.readHash(parentPos)
		if err != nil {
			return fmt.Errorf("read parent at %d: %w", parentPos, err)
		}

		// If parent equals current hash, this node has "moved up" due to sibling deletion.
		// Skip this level - the hash is already in the right place.
		if parentH == currentHash {
			currentPos = parentPos
			continue
		}

		// Read sibling hash
		sibPos := sibling(currentPos)
		sibHash, err := f.readHash(sibPos)
		if err != nil {
			return fmt.Errorf("read sibling at %d: %w", sibPos, err)
		}

		// Calculate parent hash (order depends on left/right)
		var newParentHash Hash
		if isLeftNiece(currentPos) {
			newParentHash = parentHash(currentHash, sibHash)
		} else {
			newParentHash = parentHash(sibHash, currentHash)
		}

		// Write to parent
		err = f.writeHash(parentPos, newParentHash)
		if err != nil {
			return fmt.Errorf("write parent at %d: %w", parentPos, err)
		}

		currentPos = parentPos

		prevHash := parentH
		parentPos = Parent(parentPos, f.forestRows)
		parentH, err = f.readHash(parentPos)
		if err != nil {
			return fmt.Errorf("read parent at %d: %w", parentPos, err)
		}
		for prevHash == parentH {
			// Write to parent
			err = f.writeHash(parentPos, newParentHash)
			if err != nil {
				return fmt.Errorf("write parent at %d: %w", parentPos, err)
			}

			currentPos = parentPos

			parentPos = Parent(parentPos, f.forestRows)
			parentH, err = f.readHash(parentPos)
			if err != nil {
				return fmt.Errorf("read parent at %d: %w", parentPos, err)
			}
		}
	}

	return nil
}

// Modify adds and deletes elements from the forest.
// This implements the Utreexo interface.
func (f *Forest) Modify(adds []Leaf, delHashes []Hash, _ Proof) error {
	f.mu.Lock()
	defer f.mu.Unlock()

	if f.recordMode {
		return fmt.Errorf("cannot call Modify while in record mode; call HashAll first")
	}

	// Delete first.
	if len(delHashes) > 0 {
		err := f.delete(delHashes)
		if err != nil {
			return fmt.Errorf("delete: %w", err)
		}
	}

	// Then add.
	for i, leaf := range adds {
		err := f.add(leaf.Hash, int32(i))
		if err != nil {
			return fmt.Errorf("add: %w", err)
		}
	}

	return nil
}

// ModifyAndReturnTTLs adds and deletes elements from the forest, returning
// the addIndex for each deleted leaf. This allows computing TTL (time-to-live)
// for deleted leaves. Returns -1 for leaves added via Ingest or without TTL tracking.
//
// This function is safe for concurrent access.
func (f *Forest) ModifyAndReturnTTLs(adds []Leaf, delHashes []Hash, _ Proof) ([]int32, error) {
	f.mu.Lock()
	defer f.mu.Unlock()

	if f.recordMode {
		return nil, fmt.Errorf("cannot call ModifyAndReturnTTLs while in record mode; call HashAll first")
	}

	// Collect addIndexes before deletion
	addIndexes := make([]int32, 0, len(delHashes))
	for _, delHash := range delHashes {
		packed, found, err := f.positionMap.Get(delHash)
		if err != nil {
			return nil, fmt.Errorf("positionMap.Get: %w", err)
		}
		if !found {
			return nil, fmt.Errorf("missing %v in positionMap. Cannot return ttls", delHash)
		}
		addIndexes = append(addIndexes, unpackIndex(packed))
	}

	// Delete first.
	if len(delHashes) > 0 {
		err := f.delete(delHashes)
		if err != nil {
			return nil, fmt.Errorf("delete: %w", err)
		}
	}

	// Then add.
	for i, leaf := range adds {
		err := f.add(leaf.Hash, int32(i))
		if err != nil {
			return nil, fmt.Errorf("add: %w", err)
		}
	}

	return addIndexes, nil
}

// Record adds and deletes elements without computing parent hashes.
// Use during IBD for performance - call HashAll() when done to build the tree.
// This is equivalent to Modify but defers all hashing until HashAll().
// Returns the addIndexes for deleted leaves (for TTL tracking).
func (f *Forest) Record(adds []Hash, delHashes []Hash) ([]int32, error) {
	f.mu.Lock()
	defer f.mu.Unlock()

	// Collect addIndexes and track deletions
	addIndexes := make([]int32, 0, len(delHashes))
	for _, delHash := range delHashes {
		packed, found, err := f.positionMap.Get(delHash)
		if err != nil {
			return nil, fmt.Errorf("positionMap.Get: %w", err)
		}
		if !found {
			return nil, fmt.Errorf("delhash %v not found in position map", delHash)
		}
		addIndexes = append(addIndexes, unpackIndex(packed))
		leafPos := unpackPos(packed)

		f.deletedLeafPositions.set(leafPos)
	}

	// Store leaves without computing parent hashes
	for i, hash := range adds {
		if hash != empty {
			if err := f.positionMap.Set(hash, packPosIndex(f.NumLeaves, int32(i))); err != nil {
				return nil, fmt.Errorf("positionMap.Set: %w", err)
			}
		}

		// Always write the leaf hash (even if empty, so HashAll can read it)
		err := f.writeHash(f.NumLeaves, hash)
		if err != nil {
			return nil, fmt.Errorf("write leaf: %w", err)
		}

		// Write the addIndex
		err = f.writeAddIndex(f.NumLeaves, int32(i))
		if err != nil {
			return nil, fmt.Errorf("write addIndex: %w", err)
		}

		f.NumLeaves++
	}

	f.recordMode = true
	if err := f.saveRecordMode(); err != nil {
		return nil, fmt.Errorf("save record mode: %w", err)
	}
	return addIndexes, nil
}

// HashAll computes all parent hashes after Record calls are complete.
// This builds the complete tree by iterating through all leaves and
// treating deleted positions as empty (causing siblings to move up).
func (f *Forest) HashAll() error {
	f.mu.Lock()
	defer f.mu.Unlock()

	totalLeaves := f.NumLeaves

	// Reset to rebuild from scratch
	f.NumLeaves = 0

	for pos := uint64(0); pos < totalLeaves; pos++ {
		var hash Hash
		if f.deletedLeafPositions.isSet(pos) {
			hash = empty
		} else {
			var err error
			hash, err = f.readHash(pos)
			if err != nil {
				return fmt.Errorf("read leaf at %d: %w", pos, err)
			}
		}

		// Compute parent hashes (same logic as add but without writing leaf)
		currentHash := hash
		currentPos := f.NumLeaves

		for h := uint8(0); (f.NumLeaves>>h)&1 == 1; h++ {
			rootPos := rootPosition(f.NumLeaves, h, f.forestRows)

			rootHash, err := f.readHash(rootPos)
			if err != nil {
				return fmt.Errorf("read root at row %d: %w", h, err)
			}

			// Check if this root is a deleted leaf - treat as empty if so
			if f.deletedLeafPositions.isSet(rootPos) {
				rootHash = empty
			}

			parentPos := Parent(currentPos, f.forestRows)
			newHash := parentHash(rootHash, currentHash)

			err = f.writeHash(parentPos, newHash)
			if err != nil {
				return fmt.Errorf("write parent at position %d: %w", parentPos, err)
			}

			currentHash = newHash
			currentPos = parentPos
		}

		f.NumLeaves++
	}

	f.recordMode = false
	if err := f.saveRecordMode(); err != nil {
		return fmt.Errorf("save record mode: %w", err)
	}

	return nil
}

// calculatePosition calculates the logical position of the given hash.
func (f *Forest) calculatePosition(hash Hash) (uint64, error) {
	packed, found, err := f.positionMap.Get(hash)
	if err != nil {
		return 0, fmt.Errorf("positionMap.Get: %w", err)
	}
	if !found {
		return 0, fmt.Errorf("hash %v not found in the position map", hash)
	}

	currentPos := unpackPos(packed)
	currentHash := hash
	rowsToTop := 0
	leftRightIndicator := uint64(0)
	for !isRootPositionTotalRows(currentPos, f.NumLeaves, f.forestRows) {
		parentPos := Parent(currentPos, f.forestRows)
		parentH, err := f.readHash(parentPos)
		if err != nil {
			return 0, fmt.Errorf("read parent at %d: %w", parentPos, err)
		}

		if parentH == currentHash {
			// Sibling was deleted. We don't mark at all because this level doesn't exist.
		} else {
			if isLeftNiece(currentPos) {
				// Left
				leftRightIndicator <<= 1
			} else {
				// Right
				leftRightIndicator <<= 1
				leftRightIndicator |= 1
			}
			rowsToTop++
		}
		currentPos = parentPos
		currentHash = parentH
	}

	retPos := currentPos
	for i := 0; i < rowsToTop; i++ {
		isRight := uint64(1) << i
		if leftRightIndicator&isRight == isRight {
			retPos = RightChild(retPos, f.forestRows)
		} else {
			retPos = LeftChild(retPos, f.forestRows)
		}
	}

	return retPos, nil
}

// targetPair holds both calculated position (for ordering) and actual position (for reading).
type targetPair struct {
	calcPos   uint64 // Position for sorting and sibling detection (matches pollard)
	actualPos uint64 // Position in forest file for reading hashes
}

// fetchProofHashes fetchses the needed hashes to prove the given delHashes.
func (f *Forest) fetchProofHashes(delHashes []Hash) ([]Hash, error) {
	if len(delHashes) == 0 {
		return nil, nil
	}

	// Build targets with both calculated and actual positions
	targets := make([]targetPair, 0, len(delHashes))
	for _, delHash := range delHashes {
		packed, found, err := f.positionMap.Get(delHash)
		if err != nil {
			return nil, fmt.Errorf("positionMap.Get: %w", err)
		}
		if !found {
			return nil, fmt.Errorf("hash %v not found in the position map", delHash)
		}

		calcPos, err := f.calculatePosition(delHash)
		if err != nil {
			return nil, err
		}

		targets = append(targets, targetPair{calcPos: calcPos, actualPos: unpackPos(packed)})
	}

	// Sort by calculated position to match pollard ordering
	slices.SortFunc(targets, func(a, b targetPair) bool {
		return a.calcPos < b.calcPos
	})

	// deTwin using calculated positions, accounting for move-ups in actualPos
	targets, err := f.deTwinPairs(targets)
	if err != nil {
		return nil, err
	}

	proofHashes := make([]Hash, 0, (len(targets) * int(f.forestRows+1)))
	for row := uint8(0); row <= f.forestRows; row++ {
		for i := 0; i < len(targets); i++ {
			calcPos := targets[i].calcPos
			actualPos := targets[i].actualPos

			if calcPos > maxPossiblePosAtRow(row, f.forestRows) {
				continue
			}
			if row != DetectRow(calcPos, f.forestRows) {
				continue
			}
			if isRootPositionOnRowTotalRows(calcPos, f.NumLeaves, row, f.forestRows) {
				continue
			}

			// Walk up actual position to handle move-ups
			actualParentPos := Parent(actualPos, f.forestRows)
			parentH, err := f.readHash(actualParentPos)
			if err != nil {
				return nil, err
			}
			currentHash, err := f.readHash(actualPos)
			if err != nil {
				return nil, err
			}
			for parentH == currentHash {
				actualPos = actualParentPos
				targets[i].actualPos = actualPos
				actualParentPos = Parent(actualPos, f.forestRows)
				parentH, err = f.readHash(actualParentPos)
				if err != nil {
					return nil, err
				}
			}

			// Check if next target is sibling (using calcPos)
			if i+1 < len(targets) && rightSib(calcPos) == targets[i+1].calcPos {
				targets[i].calcPos = Parent(calcPos, f.forestRows)
				targets[i].actualPos = actualParentPos
				i++ // Skip sibling
				continue
			}

			// Read sibling hash from actual sibling position
			proofHash, err := f.readHash(sibling(actualPos))
			if err != nil {
				return nil, err
			}
			proofHashes = append(proofHashes, proofHash)
			targets[i].calcPos = Parent(calcPos, f.forestRows)
			targets[i].actualPos = actualParentPos
		}

		slices.SortFunc(targets, func(a, b targetPair) bool {
			return a.calcPos < b.calcPos
		})
	}

	return proofHashes, nil
}

// deTwinPairs removes sibling pairs from targets using calculated positions.
// deTwinPairs detwins sibling pairs, updating both calcPos and actualPos.
// This is a method on Forest because actualPos needs to account for nodes
// that have moved up due to deletions (parentHash == currentHash).
func (f *Forest) deTwinPairs(targets []targetPair) ([]targetPair, error) {
	for i := 0; i < len(targets)-1; i++ {
		if targets[i].calcPos|1 == targets[i+1].calcPos {
			targets[i].calcPos = Parent(targets[i].calcPos, f.forestRows)

			// Walk up actualPos to find where the node actually is
			actualPos := targets[i].actualPos
			currentHash, err := f.readHash(actualPos)
			if err != nil {
				return nil, err
			}
			parentPos := Parent(actualPos, f.forestRows)
			parentHash, err := f.readHash(parentPos)
			if err != nil {
				return nil, err
			}
			for parentHash == currentHash {
				actualPos = parentPos
				parentPos = Parent(actualPos, f.forestRows)
				parentHash, err = f.readHash(parentPos)
				if err != nil {
					return nil, err
				}
			}
			targets[i].actualPos = parentPos

			targets = append(targets[:i+1], targets[i+2:]...)
			i--
		}
	}

	return targets, nil
}

// Prove generates an inclusion proof for the given hashes.
// This implements the Utreexo interface by looking up positions from hashes.
// Uses the walk-up algorithm to find where each hash currently is (it may have
// moved up due to deletions), then computes the proof positions.
//
// This function is safe for concurrent access.
func (f *Forest) Prove(delHashes []Hash) (Proof, error) {
	f.mu.RLock()
	defer f.mu.RUnlock()

	if len(delHashes) == 0 {
		return Proof{}, nil
	}

	// Find target positions using the walk-up algorithm.
	// calculatePosition returns positions in f.forestRows space.
	targets := make([]uint64, len(delHashes))
	for i, hash := range delHashes {
		target, err := f.calculatePosition(hash)
		if err != nil {
			return Proof{}, fmt.Errorf("find target for hash %x: %w", hash[:8], err)
		}
		targets[i] = target
	}

	// Translate from f.forestRows space to defaultForestRows space.
	if f.forestRows != defaultForestRows {
		targets = translatePositions(targets, f.forestRows, defaultForestRows)
	}

	proofHashes, err := f.fetchProofHashes(delHashes)
	if err != nil {
		return Proof{}, err
	}

	return Proof{
		Targets: targets,
		Proof:   proofHashes,
	}, nil
}

// Verify verifies that the given hashes exist in the forest.
// This implements the Utreexo interface.
//
// This function is safe for concurrent access.
func (f *Forest) Verify(delHashes []Hash, _ Proof, _ bool) error {
	f.mu.RLock()
	defer f.mu.RUnlock()

	for _, delHash := range delHashes {
		packed, found, err := f.positionMap.Get(delHash)
		if err != nil {
			return fmt.Errorf("positionMap.Get: %w", err)
		}
		if !found {
			return fmt.Errorf("hash %v doesn't exist in the forest", delHash)
		}

		if f.deletedLeafPositions.isSet(unpackPos(packed)) {
			return fmt.Errorf("hash %v has already been deleted in the forest", delHash)
		}
	}

	return nil
}

// GetLeafPosition returns the logical position for the given leaf hash.
// This implements the Utreexo interface.
//
// NOTE: Always returns (0, false) during record mode since hashes have not
// been computed yet and positions cannot be correctly calculated.
//
// This function is safe for concurrent access.
func (f *Forest) GetLeafPosition(hash Hash) (uint64, bool) {
	f.mu.RLock()
	defer f.mu.RUnlock()

	if f.recordMode {
		return 0, false
	}

	pos, err := f.calculatePosition(hash)
	if err != nil {
		return 0, false
	}

	return pos, true
}

// String returns a string representation of the forest.
// This implements the Utreexo interface.
//
// This function is safe for concurrent access.
func (f *Forest) String() string {
	// No explicit lock needed - GetHash/GetRoots/etc. take their own RLocks.
	// Nested RLocks are allowed by sync.RWMutex.
	return String(f)
}

// RawString returns a string representation of the raw file contents.
// Unlike String() which accounts for move-ups and returns the logical tree structure,
// RawString() shows the actual bytes stored at each file position. Useful for debugging.
//
// This function is safe for concurrent access.
func (f *Forest) RawString() string {
	return String(&rawForest{f})
}

// rawForest wraps Forest to provide raw file reads for GetHash.
// Unlike Forest.GetHash which traverses from root handling move-ups,
// rawForest.GetHash reads directly from the file position.
type rawForest struct {
	*Forest
}

func (r *rawForest) GetTreeRows() uint8 { return r.forestRows }

func (r *rawForest) GetHash(position uint64) Hash {
	r.mu.RLock()
	defer r.mu.RUnlock()

	hash, err := r.readHash(position)
	if err != nil {
		return empty
	}
	return hash
}
