package utreexo

import (
	"encoding/binary"
	"fmt"
	"io"
	"math/bits"
	"os"
	"path/filepath"
	"runtime"
	"sync"
	"sync/atomic"

	"github.com/utreexo/utreexo/internal/mmapfile"
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
	forestBlockCountsFileName = "forest_blockcounts.dat"  // per-block add count, 4 bytes each
	forestJournalFileName     = "forest_journal.dat"      // WAL journal for crash recovery
	forestMetaFileName        = "forest_meta.dat"         // recordMode + numLeaves + consistency hash
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
	io.WriterAt
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

// bitmapSnapshot provides a read-only, immutable view of the bitmap at
// snapshot time. It owns a private copy of the bits slice, so the writer
// can freely mutate the live bitmap without locks or COW overhead.
type bitmapSnapshot struct {
	bits []uint64 // private copy made at snapshot time; never modified
}

// isSet returns true if pos was marked as deleted at snapshot time.
func (s *bitmapSnapshot) isSet(pos uint64) bool {
	word := pos / 64
	if word >= uint64(len(s.bits)) {
		return false
	}
	return s.bits[word]&(1<<(pos%64)) != 0
}

// HashOverlay captures intermediate hash writes in memory so that
// GenRoots can write to memory while the previous GenProof still reads
// from the file. Each overlay may point to a previous overlay, forming
// a chain: reads check the chain from newest to oldest before falling
// back to the file.
//
// Within rehashDeletionsParallel, concurrent workers write to per-worker
// maps (workerData) that are merged into data after each row (under the
// wg.Wait barrier), so no locking is needed.
type HashOverlay struct {
	data map[uint64]Hash
	prev *HashOverlay // previous overlay; read-only, safe for concurrent access
}

// NewHashOverlay creates a fresh overlay. prev may be nil.
func NewHashOverlay(prev *HashOverlay) *HashOverlay {
	return &HashOverlay{
		data: make(map[uint64]Hash, 4096),
		prev: prev,
	}
}

// get retrieves a hash from the overlay chain. Returns false if not found
// in any overlay.
func (o *HashOverlay) get(pos uint64) (Hash, bool) {
	if o == nil {
		return Hash{}, false
	}
	if h, ok := o.data[pos]; ok {
		return h, true
	}
	return o.prev.get(pos)
}

// set writes a hash to this overlay.
func (o *HashOverlay) set(pos uint64, h Hash) {
	o.data[pos] = h
}

// AbsorbPrev merges prev's data into this overlay and cuts the chain.
// After this call, o.prev is nil and all entries from prev are in o.data.
// This keeps the overlay chain from growing unbounded.
//
// NOT safe for concurrent use — call only when no other goroutine reads prev.
func (o *HashOverlay) AbsorbPrev() {
	if o == nil || o.prev == nil {
		return
	}
	for pos, hash := range o.prev.data {
		if _, ok := o.data[pos]; !ok {
			o.data[pos] = hash
		}
	}
	// Recurse to absorb the entire chain.
	o.prev.AbsorbPrev()
	o.prev = nil
}

// CopyDataWithPrev creates a new overlay whose data is a shallow copy of
// this overlay's data map, with prev set to the given base overlay.
// The copy is O(len(o.data)) — only the current overlay's entries, not
// the entire chain. Used to give GenProof a private snapshot of this
// block's delta entries chained to a shared read-only base.
func (o *HashOverlay) CopyDataWithPrev(base *HashOverlay) *HashOverlay {
	if o == nil {
		return base
	}
	cp := &HashOverlay{
		data: make(map[uint64]Hash, len(o.data)),
		prev: base,
	}
	for k, v := range o.data {
		cp.data[k] = v
	}
	return cp
}

// Len returns the number of entries in this overlay (not the chain).
func (o *HashOverlay) Len() int {
	if o == nil {
		return 0
	}
	return len(o.data)
}

// FlushTo writes all entries from this overlay (not the chain) to the forest file.
func (o *HashOverlay) FlushTo(f *Forest) error {
	for pos, hash := range o.data {
		if err := f.writeHashAt(pos, hash); err != nil {
			return err
		}
	}
	return nil
}

// FlushChainTo writes all entries from this overlay AND its entire prev chain
// to the forest file. Flushes oldest-first so newer values overwrite older ones.
func (o *HashOverlay) FlushChainTo(f *Forest) error {
	if o == nil {
		return nil
	}
	// Collect chain oldest-first.
	var chain []*HashOverlay
	for cur := o; cur != nil; cur = cur.prev {
		chain = append(chain, cur)
	}
	for i := len(chain) - 1; i >= 0; i-- {
		for pos, hash := range chain[i].data {
			if err := f.writeHashAt(pos, hash); err != nil {
				return err
			}
		}
	}
	return nil
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
		// Double the capacity to amortize growth. During IBD, NumLeaves
		// increases every block and newly-added leaves may be deleted in
		// the same block, so positions steadily exceed the initial size.
		// Without doubling, every new high-water position would copy the
		// entire bitmap (O(n²) total).
		newLen := max(
			uint64(len(b.bits))*2, // amortized doubling
			max(64, word+1),       // floor of 64 words; at least enough for the requested position
		)
		newBits := make([]uint64, newLen)
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

// bitmapBufCh is a channel-based pool for snapshot buffers.
// Unlike sync.Pool, items in a buffered channel survive GC cycles.
// sync.Pool clears all cached items on every GC, which causes massive
// allocation churn when GC is already under pressure (133 GB of bitmap
// copies in ~100s of IBD). A buffered channel keeps buffers alive
// regardless of GC activity, eliminating the allocation-GC feedback loop.
var bitmapBufCh = make(chan []uint64, 64)

// snapshot creates an immutable copy of the current bitmap state.
// The returned snapshot is completely independent — the writer can
// freely mutate the live bitmap without any synchronization.
// Reuses buffers from the channel pool to avoid GC pressure.
func (b *deletedBitmap) snapshot() *bitmapSnapshot {
	needed := len(b.bits)
	var buf []uint64
	select {
	case buf = <-bitmapBufCh:
		if cap(buf) < needed {
			buf = make([]uint64, needed)
		} else {
			buf = buf[:needed]
		}
	default:
		buf = make([]uint64, needed)
	}
	copy(buf, b.bits)
	return &bitmapSnapshot{bits: buf}
}

// numWorkers is the number of goroutines used by parallelDo.
var numWorkers = runtime.NumCPU()

// workerPool is a persistent pool of goroutines. Each worker has its own
// Cond variable. Only workers with actual work are signaled, and only
// active workers are counted in the WaitGroup. Idle workers stay parked.
type workerPool struct {
	n       int
	workers []poolWorker
	wg      sync.WaitGroup
}

type poolWorker struct {
	mu    sync.Mutex
	cond  *sync.Cond
	gen   uint64
	fn    func(wIdx, start, end int)
	start int
	end   int
}

func newWorkerPool(n int) *workerPool {
	p := &workerPool{
		n:       n,
		workers: make([]poolWorker, n),
	}
	for i := 0; i < n; i++ {
		p.workers[i].cond = sync.NewCond(&p.workers[i].mu)
		go p.worker(i)
	}
	return p
}

func (p *workerPool) worker(idx int) {
	w := &p.workers[idx]
	var lastGen uint64
	w.mu.Lock()
	for {
		for w.gen == lastGen {
			w.cond.Wait()
		}
		lastGen = w.gen
		fn := w.fn
		start, end := w.start, w.end
		w.mu.Unlock()

		fn(idx, start, end)
		p.wg.Done()

		w.mu.Lock()
	}
}

func (p *workerPool) do(fn func(wIdx, start, end int), n int) {
	workers := p.n
	if workers > n {
		workers = n
	}
	chunkSize := (n + workers - 1) / workers

	active := 0
	for i := 0; i < workers; i++ {
		start := i * chunkSize
		end := start + chunkSize
		if end > n {
			end = n
		}
		if start >= end {
			break
		}
		active++
	}

	p.wg.Add(active)

	for i := 0; i < active; i++ {
		w := &p.workers[i]
		w.mu.Lock()
		w.fn = fn
		w.start = i * chunkSize
		w.end = w.start + chunkSize
		if w.end > n {
			w.end = n
		}
		w.gen++
		w.mu.Unlock()
		w.cond.Signal()
	}

	p.wg.Wait()
}

// mainPool is used by the main thread (Record, parallelLeafHash).
var mainPool = newWorkerPool(numWorkers)

// pipelinePool is used by the pipeline goroutine (GenerateRoots, GenerateProof).
var pipelinePool = newWorkerPool(numWorkers)

// parallelDo splits n work items across persistent pool workers (used by Record).
func parallelDo(fn func(wIdx, start, end int), n int) {
	mainPool.do(fn, n)
}

// MainParallelDo is an exported version of parallelDo for use by other
// packages (e.g. indexers) that need to share the main thread's worker pool.
func MainParallelDo(fn func(wIdx, start, end int), n int) {
	mainPool.do(fn, n)
}

// pipelineParallelDo splits n work items across persistent pool workers (used by GenerateRoots).
func pipelineParallelDo(fn func(wIdx, start, end int), n int) {
	pipelinePool.do(fn, n)
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

	file            forestFile
	blockCountsFile forestFile // stores uint32 add-count per block, 4 bytes each
	metaFile        forestFile // stores recordMode (bytes 0-31) + consistency hash (bytes 32-63)
	NumLeaves       uint64
	forestRows      uint8 // Fixed maximum rows for stable position mapping

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

	// lastGeneratedLeaves tracks how many leaves the last GenerateRoots
	// processed. Used to make subsequent calls incremental (O(k·log n)
	// instead of O(n)). Reset to 0 on restart.
	// Accessed atomically so GenerateRoots doesn't need f.mu.
	lastGeneratedLeaves atomic.Uint64

	// pendingDels accumulates leaf positions deleted by Record since
	// the last Snapshot. Captured by Snapshot and cleared.
	pendingDels []uint64

	// wal is set when created via OpenForest; nil for newForest (test/advanced usage).
	wal *wal

	// Reusable buffers for Record (main thread only — never accessed by pipeline).
	recordBuf      []byte     // batch write buffer for leaf hashes
	recordErrs     []error    // error collection for parallelDo
	setBatchHashes [][32]byte // reusable buffer for SetBatch hashes
	setBatchPacked []uint64   // reusable buffer for SetBatch packed values

	// closers holds os.File handles to close on Close(). Only set by OpenForest.
	closers []io.Closer
}

// readBlockCounts reads all uint32 entries from a block counts file
// and returns them as a slice.
func readBlockCounts(file io.ReadSeeker) ([]uint32, error) {
	size, err := file.Seek(0, io.SeekEnd)
	if err != nil {
		return nil, err
	}
	if size == 0 {
		return nil, nil
	}
	if size%4 != 0 {
		return nil, fmt.Errorf("block counts file size %d is not a multiple of 4", size)
	}
	if _, err := file.Seek(0, io.SeekStart); err != nil {
		return nil, err
	}
	buf := make([]byte, size)
	if _, err := io.ReadFull(file.(io.Reader), buf); err != nil {
		return nil, err
	}
	n := size / 4
	counts := make([]uint32, n)
	for i := range counts {
		counts[i] = binary.LittleEndian.Uint32(buf[i*4:])
	}
	return counts, nil
}

// newForest creates a new Forest backed by the given file.
// The file should be an io.ReadWriteSeeker (e.g., *os.File).
// blockCountsFile stores the uint32 add-count per block; numLeaves is derived
// from the cumulative sum of all block counts.
// metaFile stores recordMode (bytes 0-31), numLeaves (bytes 32-63), and consistency hash (bytes 64-95).
// bitmap tracks deleted leaf positions; pass nil for a fresh forest. When using a WAL,
// the bitmap is loaded by the WAL after recovery and passed here. For non-WAL usage,
// load it with loadDeletedBitmap.
// posMapCtrlPath and posMapSlotsPath are file paths for the Swiss Table position map.
// forestRows sets the maximum tree height (determines max leaves = 2^forestRows).
func newForest(file forestFile, blockCountsFile, metaFile forestFile, bitmap *deletedBitmap, posMapCtrlPath, posMapSlotsPath string, forestRows uint8, expectedMaxLeaves uint64) (*Forest, error) {
	if file == nil || blockCountsFile == nil || metaFile == nil {
		return nil, fmt.Errorf("one of the given files are nil")
	}

	f := &Forest{
		file:            file,
		blockCountsFile: blockCountsFile,
		metaFile:        metaFile,
		forestRows:      forestRows,
	}

	// Load metadata (recordMode + WAL-protected numLeaves).
	if err := f.loadMetadata(); err != nil {
		return nil, fmt.Errorf("load metadata: %w", err)
	}

	// Reconcile block counts file with WAL-protected numLeaves.
	// After undo-without-flush crashes, the block counts file may have
	// stale entries at the end (one per undo). Remove entries from the
	// end until the sum no longer exceeds numLeaves.
	counts, err := readBlockCounts(blockCountsFile)
	if err != nil {
		return nil, fmt.Errorf("read blockCountsFile: %w", err)
	}
	var blockTotal uint64
	for _, c := range counts {
		blockTotal += uint64(c)
	}
	for len(counts) > 0 && blockTotal > f.NumLeaves {
		blockTotal -= uint64(counts[len(counts)-1])
		counts = counts[:len(counts)-1]
	}
	if truncater, ok := blockCountsFile.(interface{ Truncate(int64) error }); ok {
		if err := truncater.Truncate(int64(len(counts)) * 4); err != nil {
			return nil, fmt.Errorf("trim block counts: %w", err)
		}
	}

	// Read consistency hash from metaFile (bytes 64-95, written atomically by WAL).
	// Zero hash on first run or if metaFile is empty.
	var consistencyHash [32]byte
	metaFile.Seek(bestHashOffset, io.SeekStart)
	metaFile.Read(consistencyHash[:])

	// Create Swiss Table for position map. Size based on numLeaves or
	// expectedMaxLeaves (whichever is larger) to avoid costly resizes.
	// When no hint is provided, use a minimum of 1<<16 to avoid excessive
	// early resizes on a fresh database. Cap at 1<<33 to prevent
	// accidental multi-hundred-GB allocations.
	expectedEntries := max(f.NumLeaves, min(expectedMaxLeaves, 1<<33))
	if expectedMaxLeaves == 0 {
		expectedEntries = max(expectedEntries, 1<<16)
	}
	posMap, needsRebuild, err := swisstable.NewSwissPositionMap(posMapCtrlPath, posMapSlotsPath, expectedEntries, consistencyHash, file, positionMask)
	if err != nil {
		return nil, fmt.Errorf("create position map: %w", err)
	}

	if bitmap == nil {
		bitmap = newDeletedBitmap(f.NumLeaves)
	}

	f.positionMap = posMap
	f.deletedLeafPositions = bitmap

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
	maxCacheMemory    int64
	expectedMaxLeaves uint64
}

// MaxCacheMemory sets the total WAL cache memory budget in bytes.
// The budget is split proportionally across files by entry size.
// If zero or not set, each file uses the WAL default (64MB).
func MaxCacheMemory(bytes int64) ForestOption {
	return func(o *forestOptions) {
		o.maxCacheMemory = bytes
	}
}

// ExpectedMaxLeaves sets the expected maximum number of leaves for presizing
// the position map. This avoids costly resizes during initial sync. If zero
// or not set, the position map is sized based on the current NumLeaves.
func ExpectedMaxLeaves(n uint64) ForestOption {
	return func(o *forestOptions) {
		o.expectedMaxLeaves = n
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
		forestBlockCountsFileName,
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

	dataFile, deletedFile, blockCountsFile, journalFile, metaFile := files[0], files[1], files[2], files[3], files[4]
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

	// On unix this memory-maps the data file for faster I/O; on other
	// platforms it falls back to the raw *os.File. The file has been
	// pre-sized above and is never resized, so the mapping is stable.
	dataFF, err := mmapfile.Open(dataFile, totalSize)
	if err != nil {
		for _, c := range closers {
			c.Close()
		}
		return nil, fmt.Errorf("open data file: %w", err)
	}
	closers[0] = dataFF

	// The block counts file is tiny (~4 bytes per block, ~3.6 MB at 900K blocks)
	// so it doesn't need a significant cache budget. Allocate the full memory
	// budget to the data file cache. Meta and block counts use WAL defaults.
	const (
		dataEntrySize        = 32
		blockCountsEntrySize = 4
		metaEntrySize        = 32
	)
	var dataCacheBytes int64
	if o.maxCacheMemory > 0 {
		dataCacheBytes = o.maxCacheMemory
	}

	wal, err := newWAL(journalFile, deletedFile,
		walFile{File: dataFF, EntrySize: dataEntrySize, MaxCacheBytes: dataCacheBytes},
		walFile{File: blockCountsFile, EntrySize: blockCountsEntrySize},
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
		o.expectedMaxLeaves,
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
		f.wal.Close()
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

// rebuildPositionMap reads all leaf hashes in batches and populates the
// positionMap. The addIndex for each leaf is derived from the block counts
// file using a linear scan (sequential access pattern).
func (f *Forest) rebuildPositionMap() error {
	if f.NumLeaves == 0 {
		return nil
	}

	// Load block counts from file into a local slice.
	blockAdds, err := readBlockCounts(f.blockCountsFile)
	if err != nil {
		return fmt.Errorf("read block counts: %w", err)
	}

	const batchSize = 4096 // entries per batch
	type batch struct {
		pos  uint64
		size uint64
		data []byte
	}

	// done is closed on any error to signal the producer goroutine to exit.
	done := make(chan struct{})
	defer close(done)

	hashCh := make(chan batch, 4)
	hashErrCh := make(chan error, 1)

	go func() {
		defer close(hashCh)

		if _, err := f.file.Seek(0, io.SeekStart); err != nil {
			hashErrCh <- err
			return
		}

		for pos := uint64(0); pos < f.NumLeaves; pos += batchSize {
			n := min(uint64(batchSize), f.NumLeaves-pos)

			buf := make([]byte, n*32)
			if _, err := io.ReadFull(f.file, buf); err != nil {
				hashErrCh <- err
				return
			}

			select {
			case hashCh <- batch{pos: pos, size: n, data: buf}:
			case <-done:
				hashErrCh <- nil
				return
			}
		}
		hashErrCh <- nil
	}()

	// Linear scan: advance blockIdx as leafPos crosses block boundaries.
	blockIdx := 0
	blockStart := uint64(0)

	for hashBatch := range hashCh {
		for i := uint64(0); i < hashBatch.size; i++ {
			leafPos := hashBatch.pos + i

			// Advance to the block containing leafPos.
			for blockIdx < len(blockAdds) && blockStart+uint64(blockAdds[blockIdx]) <= leafPos {
				blockStart += uint64(blockAdds[blockIdx])
				blockIdx++
			}
			addIndex := int32(leafPos - blockStart)

			var hash Hash
			copy(hash[:], hashBatch.data[i*32:])

			if err := f.positionMap.Set(hash, packPosIndex(leafPos, addIndex)); err != nil {
				return fmt.Errorf("positionMap.Set at %d: %w", leafPos, err)
			}
		}
	}

	// Check the hash reader for errors.
	if err := <-hashErrCh; err != nil {
		return fmt.Errorf("read hashes: %w", err)
	}

	return nil
}

// loadMetadata reads recordMode (bytes 0-31) and numLeaves (bytes 32-63)
// from the metaFile. Each field occupies one 32-byte entry.
func (f *Forest) loadMetadata() error {
	_, err := f.metaFile.Seek(0, io.SeekStart)
	if err != nil {
		return err
	}
	var buf [64]byte
	_, err = f.metaFile.Read(buf[:])
	if err == io.EOF {
		// Fresh database, no metadata yet.
		return nil
	}
	if err != nil {
		return err
	}
	f.recordMode = buf[0] != 0
	if metaLeaves := binary.LittleEndian.Uint64(buf[32:]); metaLeaves > 0 {
		f.NumLeaves = metaLeaves
	}
	return nil
}

// saveMetadata writes recordMode (bytes 0-31) and numLeaves (bytes 32-63)
// to the metaFile. Each field is written as a separate 32-byte entry to
// match the cachedRWS entry size. Both writes go through the WAL-protected
// cachedRWS, so they are crash-safe.
func (f *Forest) saveMetadata() error {
	_, err := f.metaFile.Seek(0, io.SeekStart)
	if err != nil {
		return err
	}

	var recordModeBuf [32]byte
	if f.recordMode {
		recordModeBuf[0] = 1
	}
	if _, err := f.metaFile.Write(recordModeBuf[:]); err != nil {
		return err
	}

	var numLeavesBuf [32]byte
	binary.LittleEndian.PutUint64(numLeavesBuf[:], f.NumLeaves)
	_, err = f.metaFile.Write(numLeavesBuf[:])
	return err
}

// ReadConsistencyHash reads the consistency hash from metaFile (bytes 64-95).
// The hash is written atomically by WAL.Flush().
func (f *Forest) ReadConsistencyHash() ([32]byte, error) {
	var hash [32]byte
	_, err := f.metaFile.Seek(bestHashOffset, io.SeekStart)
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

// appendBlockCount appends a block's add count to the block counts file.
func (f *Forest) appendBlockCount(count uint32) error {
	if _, err := f.blockCountsFile.Seek(0, io.SeekEnd); err != nil {
		return err
	}
	return binary.Write(f.blockCountsFile, binary.LittleEndian, count)
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

	// Persist the decremented numLeaves through the WAL-protected meta file.
	// The stale block counts entry is left on disk; it will be trimmed on
	// the next startup if a crash occurs before the next flush.
	if err := f.saveMetadata(); err != nil {
		return fmt.Errorf("save metadata: %w", err)
	}

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

	if err := f.appendBlockCount(uint32(len(adds))); err != nil {
		return fmt.Errorf("append block count: %w", err)
	}
	if err := f.saveMetadata(); err != nil {
		return fmt.Errorf("save metadata: %w", err)
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

	if err := f.appendBlockCount(uint32(len(adds))); err != nil {
		return nil, fmt.Errorf("append block count: %w", err)
	}
	if err := f.saveMetadata(); err != nil {
		return nil, fmt.Errorf("save metadata: %w", err)
	}

	return addIndexes, nil
}

// Record adds and deletes elements without computing parent hashes.
// Use during IBD for performance - call HashAll() when done to build the tree.
// This is equivalent to Modify but defers all hashing until HashAll().
// Returns the addIndexes for deleted leaves (for TTL tracking).
func (f *Forest) Record(adds []Hash, delHashes []Hash) ([]int32, []uint64, error) {
	f.mu.Lock()
	defer f.mu.Unlock()

	// Phase 1: Look up deletion positions.
	// positionMap.Get is read-only and safe for concurrent access,
	// so parallelize across cores for large batches.
	type delResult struct {
		addIndex int32
		leafPos  uint64
	}
	delResults := make([]delResult, len(delHashes))

	if nDels := len(delHashes); nDels > 0 {
		if nDels < minParallelSize {
			for i, delHash := range delHashes {
				packed, found, err := f.positionMap.Get(delHash)
				if err != nil {
					return nil, nil, fmt.Errorf("positionMap.Get: %w", err)
				}
				if !found {
					return nil, nil, fmt.Errorf("delhash %v not found in position map", delHash)
				}
				delResults[i] = delResult{unpackIndex(packed), unpackPos(packed)}
			}
		} else {
			if cap(f.recordErrs) < numWorkers {
				f.recordErrs = make([]error, numWorkers)
			}
			errs := f.recordErrs[:numWorkers]
			for i := range errs {
				errs[i] = nil
			}
			parallelDo(func(wIdx, s, e int) {
				for i := s; i < e; i++ {
					packed, found, err := f.positionMap.Get(delHashes[i])
					if err != nil {
						errs[wIdx] = fmt.Errorf("positionMap.Get: %w", err)
						return
					}
					if !found {
						errs[wIdx] = fmt.Errorf("delhash %v not found in position map", delHashes[i])
						return
					}
					delResults[i] = delResult{unpackIndex(packed), unpackPos(packed)}
				}
			}, nDels)
			for _, err := range errs {
				if err != nil {
					return nil, nil, err
				}
			}
		}
	}

	// Apply deletion results to bitmap (sequential, not thread-safe).
	addIndexes := make([]int32, len(delHashes))
	delPositions := make([]uint64, len(delHashes))
	for i, dr := range delResults {
		addIndexes[i] = dr.addIndex
		delPositions[i] = dr.leafPos
		f.deletedLeafPositions.set(dr.leafPos)
		f.pendingDels = append(f.pendingDels, dr.leafPos)
	}

	// Phase 2: Store leaves — batch file write THEN positionMap.Set.
	// The batch write must happen first because positionMap.Set may
	// trigger a Swiss table resize, which re-reads all entries from
	// the data file via verifyHash. If the leaf data isn't in the
	// cache yet, those entries would fail verification and be dropped.
	startPos := f.NumLeaves
	if len(adds) > 0 {
		needed := len(adds) * 32
		if cap(f.recordBuf) < needed {
			f.recordBuf = make([]byte, needed)
		}
		buf := f.recordBuf[:needed]
		for i, hash := range adds {
			copy(buf[i*32:(i+1)*32], hash[:])
		}
		offset := f.posToFileOffset(startPos)
		if _, err := f.file.WriteAt(buf, offset); err != nil {
			return nil, nil, fmt.Errorf("batch write leaves: %w", err)
		}
	}
	// Insert new leaves into positionMap using SetBatch (skips duplicate
	// checking since new leaves can't already exist in the table).
	if cap(f.setBatchHashes) < len(adds) {
		f.setBatchHashes = make([][32]byte, len(adds))
		f.setBatchPacked = make([]uint64, len(adds))
	}
	batchN := 0
	for i, hash := range adds {
		if hash != empty {
			f.setBatchHashes[batchN] = hash
			f.setBatchPacked[batchN] = packPosIndex(f.NumLeaves+uint64(i), int32(i))
			batchN++
		}
	}
	if batchN > 0 {
		if err := f.positionMap.SetBatch(f.setBatchHashes[:batchN], f.setBatchPacked[:batchN]); err != nil {
			return nil, nil, fmt.Errorf("positionMap.SetBatch: %w", err)
		}
	}
	f.NumLeaves += uint64(len(adds))

	if err := f.appendBlockCount(uint32(len(adds))); err != nil {
		return nil, nil, fmt.Errorf("append block count: %w", err)
	}

	f.recordMode = true
	if err := f.saveMetadata(); err != nil {
		return nil, nil, fmt.Errorf("save metadata: %w", err)
	}
	return addIndexes, delPositions, nil
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
	if err := f.saveMetadata(); err != nil {
		return fmt.Errorf("save metadata: %w", err)
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

	proofHashes := make([]Hash, 0, (len(targets) * int(TreeRows(f.NumLeaves)+1)))
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

// ForestSnapshot is an immutable view of the forest state at a point in time.
// It captures numLeaves and a COW bitmap snapshot so that a concurrent reader
// can compute roots and proofs while the writer continues calling Record.
type ForestSnapshot struct {
	numLeaves   uint64
	bitmap      *bitmapSnapshot
	pendingDels []uint64 // leaf positions deleted since last snapshot
}

// Snapshot captures the current forest state for concurrent root/proof generation.
// Only one snapshot may be active at a time. Call ReleaseSnapshot when done.
//
// The caller must ensure that all writes from prior Record calls are visible
// to ReadAt on the data file (e.g. via Flush or mmap visibility).
func (f *Forest) Snapshot() *ForestSnapshot {
	f.mu.Lock()
	defer f.mu.Unlock()
	snap := &ForestSnapshot{
		numLeaves:   f.NumLeaves,
		bitmap:      f.deletedLeafPositions.snapshot(),
		pendingDels: f.pendingDels,
	}
	f.pendingDels = nil
	return snap
}

// ReleaseSnapshot returns the snapshot's bitmap buffer to the channel pool
// for reuse, reducing GC pressure from per-block bitmap copies. Should be
// called after GenerateRoots and GenerateProof are done using the snapshot.
func (f *Forest) ReleaseSnapshot(snap *ForestSnapshot) {
	if snap == nil || snap.bitmap == nil || snap.bitmap.bits == nil {
		return
	}
	select {
	case bitmapBufCh <- snap.bitmap.bits:
	default:
		// Channel full — let GC collect this buffer.
	}
	snap.bitmap.bits = nil
}

// FlushOverlay writes all entries from the overlay to the file/cache and
// clears the overlay. This bounds overlay memory during long pipeline runs.
//
// Must be called when no other goroutine is reading from the overlay or
// from the file positions being written.
func (f *Forest) FlushOverlay(overlay *HashOverlay) error {
	if overlay == nil {
		return nil
	}
	for pos, hash := range overlay.data {
		if err := f.writeHashAt(pos, hash); err != nil {
			return fmt.Errorf("FlushOverlay write pos %d: %w", pos, err)
		}
	}
	// Clear the overlay data but keep the struct so callers with a
	// reference can still use it (it will just be empty).
	clear(overlay.data)
	overlay.prev = nil
	return nil
}

// WriteOverlayToFile writes all entries from the overlay to the file/cache
// WITHOUT clearing the overlay data. Use this when other goroutines may
// still hold references to the overlay via prev chains.
func (f *Forest) WriteOverlayToFile(overlay *HashOverlay) error {
	if overlay == nil {
		return nil
	}
	for pos, hash := range overlay.data {
		if err := f.writeHashAt(pos, hash); err != nil {
			return fmt.Errorf("WriteOverlayToFile write pos %d: %w", pos, err)
		}
	}
	return nil
}

// readHashAt reads the hash at the given position using ReadAt.
// Unlike readHash, this does not use the seek position and is safe for
// concurrent use with other ReadAt/WriteAt calls on disjoint positions.
func (f *Forest) readHashAt(position uint64) (Hash, error) {
	offset := f.posToFileOffset(position)
	var hash Hash
	_, err := f.file.ReadAt(hash[:], offset)
	if err != nil {
		return Hash{}, err
	}
	return hash, nil
}

// readHashWithOverlay reads the hash at the given position, checking the
// overlay chain first. Falls back to the file if not found in any overlay.
func (f *Forest) readHashWithOverlay(position uint64, overlay *HashOverlay) (Hash, error) {
	if h, ok := overlay.get(position); ok {
		return h, nil
	}
	return f.readHashAt(position)
}

// writeHashAt writes the hash at the given position using WriteAt.
// Unlike writeHash, this does not use the seek position and is safe for
// concurrent use with other ReadAt/WriteAt calls on disjoint positions.
func (f *Forest) writeHashAt(position uint64, hash Hash) error {
	offset := f.posToFileOffset(position)
	_, err := f.file.WriteAt(hash[:], offset)
	return err
}

// GenerateRoots computes all intermediate hashes and returns the roots for
// the forest state captured in snap. It reads leaf hashes from row 0
// (which are immutable once written by Record) and writes intermediate
// hashes to rows 1+ using WriteAt. Since Record only appends to row 0
// beyond snap.numLeaves, there is no I/O contention with a concurrent writer.
//
// This method does NOT hold f.mu — it is safe to call concurrently with Record.
func (f *Forest) GenerateRoots(snap *ForestSnapshot) ([]Hash, uint64, error) {
	totalLeaves := snap.numLeaves
	prevLeaves := f.lastGeneratedLeaves.Load()

	if prevLeaves == 0 || prevLeaves > totalLeaves {
		// First call or restart: full O(n) scan.
		return f.generateRootsFull(snap)
	}

	// Incremental: O(k·log n) — only process new adds + deletions.
	return f.generateRootsIncremental(snap, prevLeaves)
}

// GenerateRootsOverlay is like GenerateRoots but writes intermediate hashes
// to an in-memory overlay instead of the file. This allows the caller to
// release the snapshot immediately and run GenProof from the overlay while
// the next block's GenRoots runs concurrently.
//
// prevOverlay is the previous block's overlay (may be nil); it's checked
// before the file for reads so that unflushed writes from the previous
// GenRoots are visible.
//
// Returns the roots, numLeaves, and the overlay containing all writes.
func (f *Forest) GenerateRootsOverlay(snap *ForestSnapshot, prevOverlay *HashOverlay) ([]Hash, uint64, *HashOverlay, error) {
	totalLeaves := snap.numLeaves
	forestRows := f.forestRows
	overlay := NewHashOverlay(prevOverlay)
	prevLeaves := f.lastGeneratedLeaves.Load()

	if prevLeaves == 0 || prevLeaves > totalLeaves {
		roots, numLeaves, err := f.generateRootsFullOverlay(snap, overlay)
		return roots, numLeaves, overlay, err
	}

	roots, numLeaves, err := f.generateRootsIncrementalOverlay(snap, prevLeaves, overlay)
	if err != nil {
		return nil, 0, nil, err
	}

	_ = forestRows
	return roots, numLeaves, overlay, nil
}

// generateRootsFullOverlay is like generateRootsFull but writes to overlay.
func (f *Forest) generateRootsFullOverlay(snap *ForestSnapshot, overlay *HashOverlay) ([]Hash, uint64, error) {
	totalLeaves := snap.numLeaves
	forestRows := f.forestRows

	var numLeaves uint64
	for pos := uint64(0); pos < totalLeaves; pos++ {
		var hash Hash
		if snap.bitmap.isSet(pos) {
			hash = empty
		} else {
			var err error
			hash, err = f.readHashWithOverlay(pos, overlay)
			if err != nil {
				return nil, 0, fmt.Errorf("read leaf at %d: %w", pos, err)
			}
		}

		currentHash := hash
		currentPos := numLeaves
		for h := uint8(0); (numLeaves>>h)&1 == 1; h++ {
			rootPos := rootPosition(numLeaves, h, forestRows)
			rootHash, err := f.readHashWithOverlay(rootPos, overlay)
			if err != nil {
				return nil, 0, fmt.Errorf("read root at row %d: %w", h, err)
			}
			if snap.bitmap.isSet(rootPos) {
				rootHash = empty
			}

			parentPos := Parent(currentPos, forestRows)
			newHash := parentHash(rootHash, currentHash)
			overlay.set(parentPos, newHash)

			currentHash = newHash
			currentPos = parentPos
		}
		numLeaves++
	}

	f.lastGeneratedLeaves.Store(totalLeaves)

	return f.collectRootsOverlay(snap, numLeaves, overlay)
}

// generateRootsIncrementalOverlay is like generateRootsIncremental but writes to overlay.
func (f *Forest) generateRootsIncrementalOverlay(snap *ForestSnapshot, prevLeaves uint64, overlay *HashOverlay) ([]Hash, uint64, error) {
	totalLeaves := snap.numLeaves
	forestRows := f.forestRows

	// Phase 1: Rehash deletion paths using overlay.
	if err := f.rehashDeletionsOverlay(snap, totalLeaves, forestRows, overlay); err != nil {
		return nil, 0, err
	}

	// Phase 2: Process new additions.
	numLeaves := prevLeaves
	for pos := prevLeaves; pos < totalLeaves; pos++ {
		var hash Hash
		if snap.bitmap.isSet(pos) {
			hash = empty
		} else {
			var err error
			hash, err = f.readHashWithOverlay(pos, overlay)
			if err != nil {
				return nil, 0, fmt.Errorf("read leaf at %d: %w", pos, err)
			}
		}

		currentHash := hash
		currentPos := numLeaves
		for h := uint8(0); (numLeaves>>h)&1 == 1; h++ {
			rootPos := rootPosition(numLeaves, h, forestRows)
			rootHash, err := f.readHashWithOverlay(rootPos, overlay)
			if err != nil {
				return nil, 0, fmt.Errorf("read root at row %d: %w", h, err)
			}
			if snap.bitmap.isSet(rootPos) {
				rootHash = empty
			}

			parentPos := Parent(currentPos, forestRows)
			newHash := parentHash(rootHash, currentHash)
			overlay.set(parentPos, newHash)

			currentHash = newHash
			currentPos = parentPos
		}
		numLeaves++
	}

	f.lastGeneratedLeaves.Store(totalLeaves)

	return f.collectRootsOverlay(snap, numLeaves, overlay)
}

// rehashDeletionsOverlay is like rehashDeletionsParallel but writes to overlay.
func (f *Forest) rehashDeletionsOverlay(snap *ForestSnapshot, numLeaves uint64, forestRows uint8, overlay *HashOverlay) error {
	if len(snap.pendingDels) == 0 {
		return nil
	}

	numWorkers := runtime.NumCPU()
	affected := make([]uint64, len(snap.pendingDels))
	copy(affected, snap.pendingDels)
	slices.SortFunc(affected, func(a, b uint64) bool { return a < b })

	parentOut := make([]uint64, len(affected))
	nextAffected := make([]uint64, 0, len(affected))
	errs := make([]error, numWorkers)

	// Per-worker overlay maps to avoid concurrent map writes.
	workerMaps := make([]map[uint64]Hash, numWorkers)
	for w := range workerMaps {
		workerMaps[w] = make(map[uint64]Hash, len(affected)/numWorkers+1)
	}

	for row := uint8(0); row < forestRows && len(affected) > 0; row++ {
		n := len(affected)

		// Deduplicate sibling pairs.
		for i := 0; i < n-1; i++ {
			if affected[i] == ^uint64(0) {
				continue
			}
			if affected[i]^1 == affected[i+1] {
				affected[i] = leftSib(affected[i])
				affected[i+1] = ^uint64(0)
			}
		}
		j := 0
		for i := 0; i < n; i++ {
			if affected[i] != ^uint64(0) {
				affected[j] = affected[i]
				j++
			}
		}
		affected = affected[:j]
		n = j
		if n == 0 {
			break
		}

		if cap(parentOut) < n {
			parentOut = make([]uint64, n)
		}
		parentOut = parentOut[:n]

		rehashOverlayWork := func(wIdx, s, e int) {
			wm := workerMaps[wIdx]
			for i := s; i < e; i++ {
				pos := affected[i]

				if isRootPositionTotalRows(pos, numLeaves, forestRows) {
					if row == 0 {
						wm[pos] = empty
					}
					parentOut[i] = ^uint64(0)
					continue
				}

				var currentHash Hash
				if row == 0 && snap.bitmap.isSet(pos) {
					currentHash = empty
				} else {
					h, err := f.readHashWithOverlay(pos, overlay)
					if err != nil {
						currentHash = empty
					} else {
						currentHash = h
					}
				}

				sibPos := sibling(pos)
				sibHash, err := f.readHashWithOverlay(sibPos, overlay)
				if err != nil {
					sibHash = empty
				}
				if row == 0 && snap.bitmap.isSet(sibPos) {
					sibHash = empty
				}

				parentPos := Parent(pos, forestRows)
				var newHash Hash
				if isLeftNiece(pos) {
					newHash = parentHash(currentHash, sibHash)
				} else {
					newHash = parentHash(sibHash, currentHash)
				}
				wm[parentPos] = newHash
				parentOut[i] = parentPos
			}
		}

		if n < minParallelSize {
			clear(workerMaps[0])
			rehashOverlayWork(0, 0, n)
		} else {
			workers := numWorkers
			if workers > n {
				workers = n
			}
			for w := 0; w < workers; w++ {
				clear(workerMaps[w])
			}
			for i := range errs {
				errs[i] = nil
			}
			pipelineParallelDo(func(wIdx, s, e int) {
				rehashOverlayWork(wIdx, s, e)
			}, n)
			for _, err := range errs {
				if err != nil {
					return err
				}
			}
		}

		// Merge worker maps into main overlay.
		mergeWorkers := numWorkers
		if n < minParallelSize {
			mergeWorkers = 1
		} else if mergeWorkers > n {
			mergeWorkers = n
		}
		for w := 0; w < mergeWorkers; w++ {
			for pos, hash := range workerMaps[w] {
				overlay.set(pos, hash)
			}
		}

		// Collect unique parent positions for next row.
		nextAffected = nextAffected[:0]
		for i := 0; i < n; i++ {
			if parentOut[i] != ^uint64(0) {
				nextAffected = append(nextAffected, parentOut[i])
			}
		}
		slices.SortFunc(nextAffected, func(a, b uint64) bool { return a < b })
		j = 0
		for i := 0; i < len(nextAffected); i++ {
			if i == 0 || nextAffected[i] != nextAffected[i-1] {
				nextAffected[j] = nextAffected[i]
				j++
			}
		}
		nextAffected = nextAffected[:j]
		affected, nextAffected = nextAffected, affected
	}

	return nil
}

// collectRootsOverlay reads root hashes from overlay → file.
func (f *Forest) collectRootsOverlay(snap *ForestSnapshot, numLeaves uint64, overlay *HashOverlay) ([]Hash, uint64, error) {
	rootPositions := RootPositions(numLeaves, f.forestRows)
	roots := make([]Hash, len(rootPositions))
	for i, pos := range rootPositions {
		if snap.bitmap.isSet(pos) {
			roots[i] = empty
			continue
		}
		hash, err := f.readHashWithOverlay(pos, overlay)
		if err != nil {
			return nil, 0, fmt.Errorf("read root at position %d: %w", pos, err)
		}
		roots[i] = hash
	}
	return roots, numLeaves, nil
}

// GenerateProofFromOverlay builds a proof reading from the overlay → file.
// Safe to call concurrently with another GenRoots that writes to a different overlay.
func (f *Forest) GenerateProofFromOverlay(targets []uint64, snap *ForestSnapshot, overlay *HashOverlay) (Proof, error) {
	if len(targets) == 0 {
		return Proof{}, nil
	}

	numLeaves := snap.numLeaves
	forestRows := f.forestRows

	proofHashes, err := f.fetchProofHashesOverlay(targets, numLeaves, snap, overlay)
	if err != nil {
		return Proof{}, err
	}

	outTargets := make([]uint64, len(targets))
	copy(outTargets, targets)
	if forestRows != defaultForestRows {
		outTargets = translatePositions(outTargets, forestRows, defaultForestRows)
	}

	return Proof{
		Targets: outTargets,
		Proof:   proofHashes,
	}, nil
}

// fetchProofHashesOverlay fetches proof hashes reading from overlay → file.
// Parallelizes reads within each row.
func (f *Forest) fetchProofHashesOverlay(leafPositions []uint64, numLeaves uint64, snap *ForestSnapshot, overlay *HashOverlay) ([]Hash, error) {
	if len(leafPositions) == 0 {
		return nil, nil
	}

	forestRows := f.forestRows
	targets := make([]uint64, len(leafPositions))
	copy(targets, leafPositions)
	slices.SortFunc(targets, func(a, b uint64) bool { return a < b })
	targets = deTwin(targets, forestRows)

	numWorkers := runtime.NumCPU()
	proofHashes := make([]Hash, 0, len(targets)*int(TreeRows(numLeaves)+1))

	for row := uint8(0); row <= forestRows; row++ {
		type readWork struct {
			targetIdx int
			sibPos    uint64
		}
		var reads []readWork

		for i := 0; i < len(targets); i++ {
			pos := targets[i]
			if pos > maxPossiblePosAtRow(row, forestRows) {
				continue
			}
			if row != DetectRow(pos, forestRows) {
				continue
			}
			if isRootPositionOnRowTotalRows(pos, numLeaves, row, forestRows) {
				continue
			}
			if i+1 < len(targets) && rightSib(pos) == targets[i+1] {
				targets[i] = Parent(pos, forestRows)
				i++
				continue
			}
			reads = append(reads, readWork{targetIdx: i, sibPos: sibling(pos)})
			targets[i] = Parent(pos, forestRows)
		}

		if len(reads) == 0 {
			continue
		}

		rowHashes := make([]Hash, len(reads))
		nReads := len(reads)

		if nReads < minParallelSize {
			for j, r := range reads {
				h, err := f.readHashForProofOverlay(r.sibPos, snap, overlay)
				if err != nil {
					return nil, err
				}
				rowHashes[j] = h
			}
		} else {
			errs := make([]error, numWorkers)
			pipelineParallelDo(func(wIdx, s, e int) {
				for j := s; j < e; j++ {
					h, err := f.readHashForProofOverlay(reads[j].sibPos, snap, overlay)
					if err != nil {
						errs[wIdx] = err
						return
					}
					rowHashes[j] = h
				}
			}, nReads)
			for _, err := range errs {
				if err != nil {
					return nil, err
				}
			}
		}

		proofHashes = append(proofHashes, rowHashes...)
		slices.SortFunc(targets, func(a, b uint64) bool { return a < b })
	}

	return proofHashes, nil
}

// readHashForProofOverlay reads a hash for proof generation using overlay → file.
func (f *Forest) readHashForProofOverlay(position uint64, snap *ForestSnapshot, overlay *HashOverlay) (Hash, error) {
	if DetectRow(position, f.forestRows) == 0 && snap.bitmap.isSet(position) {
		return empty, nil
	}
	return f.readHashWithOverlay(position, overlay)
}

// generateRootsFull rebuilds all intermediate hashes from scratch.
// O(n) — used only on the first call after startup.
func (f *Forest) generateRootsFull(snap *ForestSnapshot) ([]Hash, uint64, error) {
	totalLeaves := snap.numLeaves
	forestRows := f.forestRows

	// Full scan: process all leaves [0, totalLeaves) in parallel.
	if err := f.processAddsParallel(snap, 0, totalLeaves, forestRows); err != nil {
		return nil, 0, err
	}

	f.lastGeneratedLeaves.Store(totalLeaves)

	return f.collectRoots(snap, totalLeaves)
}

// generateRootsIncremental updates intermediate hashes for only the new
// additions and deletions since the last GenerateRoots call.
// O(k·log n) where k = new adds + new deletions.
func (f *Forest) generateRootsIncremental(snap *ForestSnapshot, prevLeaves uint64) ([]Hash, uint64, error) {
	totalLeaves := snap.numLeaves
	forestRows := f.forestRows

	// Phase 1: Rehash deletion paths row-by-row in parallel.
	// At each row, compute parent hashes for all affected positions
	// concurrently using ReadAt/WriteAt on disjoint file offsets.
	// Uses sorted slices (not maps) to avoid GC pressure.
	if err := f.rehashDeletionsParallel(snap, totalLeaves, forestRows); err != nil {
		return nil, 0, err
	}

	// Phase 2: Process new additions row-by-row in parallel.
	// New leaf positions form a contiguous range [prevLeaves, totalLeaves).
	// At each row, sibling pairs are deduplicated and parent hashes are
	// computed concurrently across all cores. This replaces the sequential
	// per-leaf merge loop with a parallel bottom-up tree build.
	if err := f.processAddsParallel(snap, prevLeaves, totalLeaves, forestRows); err != nil {
		return nil, 0, err
	}

	f.lastGeneratedLeaves.Store(totalLeaves)

	return f.collectRoots(snap, totalLeaves)
}


// rehashDeletionsParallel recomputes intermediate hashes for all pending
// deletions, processing the tree row by row from bottom up. At each row,
// all affected positions are processed in parallel using goroutines.
//
// To avoid write conflicts when two deletions share an ancestor, sibling
// pairs are deduplicated: if both left and right sibling are affected,
// only the left is kept (it reads both children). Uses sorted slices
// instead of maps to minimize GC pressure.
// minParallelSize is the minimum number of work items before we
// spawn goroutines. Below this threshold, the goroutine launch/sync
// overhead exceeds the benefit of parallelism.
const minParallelSize = 4096

func (f *Forest) rehashDeletionsParallel(snap *ForestSnapshot, numLeaves uint64, forestRows uint8) error {
	if len(snap.pendingDels) == 0 {
		return nil
	}

	numWorkers := runtime.NumCPU()

	// Affected positions at the current row. Reuse slices across rows.
	affected := make([]uint64, len(snap.pendingDels))
	copy(affected, snap.pendingDels)
	slices.SortFunc(affected, func(a, b uint64) bool { return a < b })

	// parentOut[i] holds the parent position computed for affected[i].
	// Separate from affected to avoid data races between goroutines.
	parentOut := make([]uint64, len(affected))
	nextAffected := make([]uint64, 0, len(affected))
	errs := make([]error, numWorkers)

	for row := uint8(0); row < forestRows && len(affected) > 0; row++ {
		n := len(affected)

		// Deduplicate sibling pairs: if both pos and sibling(pos) are
		// in the list, keep only the left sibling (it will read both
		// children). Mark the right sibling as ^0 (sentinel).
		for i := 0; i < n-1; i++ {
			if affected[i] == ^uint64(0) {
				continue
			}
			if affected[i]^1 == affected[i+1] {
				affected[i] = leftSib(affected[i])
				affected[i+1] = ^uint64(0)
			}
		}

		// Compact: remove sentinels.
		j := 0
		for i := 0; i < n; i++ {
			if affected[i] != ^uint64(0) {
				affected[j] = affected[i]
				j++
			}
		}
		affected = affected[:j]
		n = j

		if n == 0 {
			break
		}

		// Ensure parentOut is large enough.
		if cap(parentOut) < n {
			parentOut = make([]uint64, n)
		}
		parentOut = parentOut[:n]

		// rehashDeletionWork processes positions [s, e) for the current row.
		rehashDeletionWork := func(s, e int) error {
			for i := s; i < e; i++ {
				pos := affected[i]

				if isRootPositionTotalRows(pos, numLeaves, forestRows) {
					if row == 0 {
						_ = f.writeHashAt(pos, empty)
					}
					parentOut[i] = ^uint64(0) // no parent to propagate
					continue
				}

				// Read current position's hash.
				var currentHash Hash
				if row == 0 && snap.bitmap.isSet(pos) {
					currentHash = empty
				} else {
					h, err := f.readHashAt(pos)
					if err != nil {
						currentHash = empty
					} else {
						currentHash = h
					}
				}

				sibPos := sibling(pos)
				sibHash, err := f.readHashAt(sibPos)
				if err != nil {
					sibHash = empty
				}
				if row == 0 && snap.bitmap.isSet(sibPos) {
					sibHash = empty
				}

				parentPos := Parent(pos, forestRows)
				var newHash Hash
				if isLeftNiece(pos) {
					newHash = parentHash(currentHash, sibHash)
				} else {
					newHash = parentHash(sibHash, currentHash)
				}

				if err := f.writeHashAt(parentPos, newHash); err != nil {
					return err
				}
				parentOut[i] = parentPos
			}
			return nil
		}

		if n < minParallelSize {
			if err := rehashDeletionWork(0, n); err != nil {
				return err
			}
		} else {
			for i := range errs {
				errs[i] = nil
			}
			pipelineParallelDo(func(wIdx, s, e int) {
				errs[wIdx] = rehashDeletionWork(s, e)
			}, n)
			for _, err := range errs {
				if err != nil {
					return err
				}
			}
		}

		// Collect unique parent positions for the next row.
		nextAffected = nextAffected[:0]
		for i := 0; i < n; i++ {
			if parentOut[i] != ^uint64(0) {
				nextAffected = append(nextAffected, parentOut[i])
			}
		}
		slices.SortFunc(nextAffected, func(a, b uint64) bool { return a < b })
		// Deduplicate consecutive equal values.
		j = 0
		for i := 0; i < len(nextAffected); i++ {
			if i == 0 || nextAffected[i] != nextAffected[i-1] {
				nextAffected[j] = nextAffected[i]
				j++
			}
		}
		nextAffected = nextAffected[:j]

		affected, nextAffected = nextAffected, affected
	}

	return nil
}

// processAddsParallel computes intermediate hashes for new additions
// [prevLeaves, totalLeaves) using a parallel bottom-up approach.
// At each row, all parent hashes are computed concurrently across cores.
//
// The approach mirrors rehashDeletionsParallel: start with the new leaf
// positions as "affected" at row 0, deduplicate sibling pairs, compute
// parents in parallel, and propagate parent positions to the next row.
//
// For deduplicated pairs (both children are new), both hashes come from
// the file. For singles (one new child, one existing sibling), the existing
// sibling's hash is read from the file (already correct from Phase 1 deletion
// rehashing). Deleted row-0 leaves are treated as empty via the snapshot bitmap.
func (f *Forest) processAddsParallel(snap *ForestSnapshot, prevLeaves, totalLeaves uint64, forestRows uint8) error {
	numAdds := int(totalLeaves - prevLeaves)
	if numAdds == 0 {
		return nil
	}

	numWorkers := runtime.NumCPU()

	// Start with new leaf positions (contiguous, already sorted).
	affected := make([]uint64, numAdds)
	for i := range affected {
		affected[i] = prevLeaves + uint64(i)
	}

	parentOut := make([]uint64, numAdds)
	nextAffected := make([]uint64, 0, numAdds)
	errs := make([]error, numWorkers)

	for row := uint8(0); row < forestRows && len(affected) > 0; row++ {
		n := len(affected)

		// Deduplicate sibling pairs: if both left and right sibling are
		// affected, keep only the left sibling. It will read both children.
		for i := 0; i < n-1; i++ {
			if affected[i] == ^uint64(0) {
				continue
			}
			if affected[i]^1 == affected[i+1] {
				affected[i] = leftSib(affected[i])
				affected[i+1] = ^uint64(0)
			}
		}
		j := 0
		for i := 0; i < n; i++ {
			if affected[i] != ^uint64(0) {
				affected[j] = affected[i]
				j++
			}
		}
		affected = affected[:j]
		n = j
		if n == 0 {
			break
		}

		if cap(parentOut) < n {
			parentOut = make([]uint64, n)
		}
		parentOut = parentOut[:n]

		// processAddsWork processes positions [s, e) for the current row.
		processAddsWork := func(s, e int) error {
			for i := s; i < e; i++ {
				pos := affected[i]

				if isRootPositionTotalRows(pos, totalLeaves, forestRows) {
					parentOut[i] = ^uint64(0) // no parent to propagate
					continue
				}

				// Read both children of the parent.
				lPos := leftSib(pos)
				rPos := lPos | 1

				var leftHash, rightHash Hash

				if row == 0 && snap.bitmap.isSet(lPos) {
					leftHash = empty
				} else {
					h, err := f.readHashAt(lPos)
					if err != nil {
						leftHash = empty
					} else {
						leftHash = h
					}
				}

				if row == 0 && snap.bitmap.isSet(rPos) {
					rightHash = empty
				} else {
					h, err := f.readHashAt(rPos)
					if err != nil {
						rightHash = empty
					} else {
						rightHash = h
					}
				}

				parentPos := Parent(pos, forestRows)
				newHash := parentHash(leftHash, rightHash)

				if err := f.writeHashAt(parentPos, newHash); err != nil {
					return err
				}
				parentOut[i] = parentPos
			}
			return nil
		}

		if n < minParallelSize {
			if err := processAddsWork(0, n); err != nil {
				return err
			}
		} else {
			for i := range errs {
				errs[i] = nil
			}
			pipelineParallelDo(func(wIdx, s, e int) {
				errs[wIdx] = processAddsWork(s, e)
			}, n)
			for _, err := range errs {
				if err != nil {
					return err
				}
			}
		}

		// Collect unique parent positions for the next row.
		nextAffected = nextAffected[:0]
		for i := 0; i < n; i++ {
			if parentOut[i] != ^uint64(0) {
				nextAffected = append(nextAffected, parentOut[i])
			}
		}
		slices.SortFunc(nextAffected, func(a, b uint64) bool { return a < b })
		j = 0
		for i := 0; i < len(nextAffected); i++ {
			if i == 0 || nextAffected[i] != nextAffected[i-1] {
				nextAffected[j] = nextAffected[i]
				j++
			}
		}
		nextAffected = nextAffected[:j]
		affected, nextAffected = nextAffected, affected
	}

	return nil
}

// collectRoots reads root hashes from the file, respecting the snapshot bitmap.
func (f *Forest) collectRoots(snap *ForestSnapshot, numLeaves uint64) ([]Hash, uint64, error) {
	rootPositions := RootPositions(numLeaves, f.forestRows)
	roots := make([]Hash, len(rootPositions))
	for i, pos := range rootPositions {
		if snap.bitmap.isSet(pos) {
			roots[i] = empty
			continue
		}
		hash, err := f.readHashAt(pos)
		if err != nil {
			return nil, 0, fmt.Errorf("read root at position %d: %w", pos, err)
		}
		roots[i] = hash
	}

	return roots, numLeaves, nil
}

// ExitRecordMode transitions the forest out of record mode after GenerateRoots
// has written all intermediate hashes to the data file. This allows subsequent
// calls to Modify, Prove, and other methods that require a fully-hashed tree.
//
// The caller must have called GenerateRoots (with a snapshot covering all
// recorded leaves) before calling this method, so that intermediate hashes
// are populated in the data file.
func (f *Forest) ExitRecordMode() error {
	f.mu.Lock()
	defer f.mu.Unlock()

	if !f.recordMode {
		return nil
	}

	f.recordMode = false
	if err := f.saveMetadata(); err != nil {
		return fmt.Errorf("save metadata: %w", err)
	}
	return nil
}

// IsRecordMode returns true if the forest is in record mode (Record has been
// called but intermediate hashes have not yet been computed).
func (f *Forest) IsRecordMode() bool {
	f.mu.RLock()
	defer f.mu.RUnlock()
	return f.recordMode
}

// getLeafPosition returns the row-0 position for the given hash from the
// position map. Unlike calculatePosition (used with Modify), no walk-up is
// needed because GenerateRoots has no move-ups — every leaf stays at its
// original row-0 position.
func (f *Forest) getLeafPosition(hash Hash) (uint64, error) {
	packed, found, err := f.positionMap.Get(hash)
	if err != nil {
		return 0, fmt.Errorf("positionMap.Get: %w", err)
	}
	if !found {
		return 0, fmt.Errorf("hash %v not found in the position map", hash)
	}
	return unpackPos(packed), nil
}

// readHashForProof reads the hash at the given position, respecting the
// snapshot bitmap: deleted row-0 leaves return empty (since GenerateRoots
// treats them as empty but doesn't overwrite their file position).
func (f *Forest) readHashForProof(position uint64, snap *ForestSnapshot) (Hash, error) {
	if DetectRow(position, f.forestRows) == 0 && snap.bitmap.isSet(position) {
		return empty, nil
	}
	return f.readHashAt(position)
}

// GenerateProof generates an inclusion proof for the given hashes using the
// forest state captured in snap. GenerateRoots must have been called on the
// same snapshot first so that intermediate hashes are populated.
//
// The proof targets are row-0 positions in the GenerateRoots tree (no move-ups),
// translated to defaultForestRows space.
//
// This method does NOT hold f.mu — it is safe to call concurrently with Record.
func (f *Forest) GenerateProof(snap *ForestSnapshot, delHashes []Hash) (Proof, error) {
	if len(delHashes) == 0 {
		return Proof{}, nil
	}

	forestRows := f.forestRows

	// Build target pairs: calcPos for ordering, actualPos (raw leaf pos) for reading.
	pairs := make([]targetPair, len(delHashes))
	for i, hash := range delHashes {
		rawPos, err := f.getLeafPosition(hash)
		if err != nil {
			return Proof{}, fmt.Errorf("find target for hash %x: %w", hash[:8], err)
		}
		calcPos, err := f.calculatePositionAt(rawPos, snap)
		if err != nil {
			return Proof{}, fmt.Errorf("calculatePositionAt for hash %x: %w", hash[:8], err)
		}
		pairs[i] = targetPair{calcPos: calcPos, actualPos: rawPos}
	}

	proofHashes, err := f.fetchProofHashesPairsAt(pairs, snap)
	if err != nil {
		return Proof{}, err
	}

	// Output targets use calcPos.
	targets := make([]uint64, len(pairs))
	for i, p := range pairs {
		targets[i] = p.calcPos
	}
	if forestRows != defaultForestRows {
		targets = translatePositions(targets, forestRows, defaultForestRows)
	}

	return Proof{
		Targets: targets,
		Proof:   proofHashes,
	}, nil
}

// LookupDelPositions resolves deletion hashes to their leaf positions via the
// position map. Call this BEFORE releasing the snapshot so the position map is
// not mutated concurrently by Record.
func (f *Forest) LookupDelPositions(delHashes []Hash) ([]uint64, error) {
	n := len(delHashes)
	if n == 0 {
		return nil, nil
	}
	positions := make([]uint64, n)

	// positionMap.Get is safe for concurrent read-only access.
	numWorkers := runtime.NumCPU()
	if numWorkers > n {
		numWorkers = n
	}
	if numWorkers <= 1 {
		for i, hash := range delHashes {
			pos, err := f.getLeafPosition(hash)
			if err != nil {
				return nil, fmt.Errorf("find target for hash %x: %w", hash[:8], err)
			}
			positions[i] = pos
		}
		return positions, nil
	}

	errs := make([]error, numWorkers)
	chunkSize := (n + numWorkers - 1) / numWorkers
	var wg sync.WaitGroup
	for w := 0; w < numWorkers; w++ {
		start := w * chunkSize
		end := start + chunkSize
		if end > n {
			end = n
		}
		if start >= end {
			continue
		}
		wg.Add(1)
		go func(wIdx, s, e int) {
			defer wg.Done()
			for i := s; i < e; i++ {
				pos, err := f.getLeafPosition(delHashes[i])
				if err != nil {
					errs[wIdx] = fmt.Errorf("find target for hash %x: %w", delHashes[i][:8], err)
					return
				}
				positions[i] = pos
			}
		}(w, start, end)
	}
	wg.Wait()
	for _, err := range errs {
		if err != nil {
			return nil, err
		}
	}
	return positions, nil
}

// GenerateProofFromPositions builds an inclusion proof using pre-computed
// leaf positions. Unlike GenerateProof, it does NOT access the position map,
// so it is safe to call concurrently with Record (which writes to positionMap).
// It only reads from the data file and the bitmap snapshot.
//
// Because GenerateRoots builds the tree without move-ups (deleted leaves are
// empty, parentHash(empty, x) = x propagates naturally), we use a two-position
// scheme: calcPos (from calculatePositionAt) determines row ordering and sibling
// detection (matching what a pollard sees), while actualPos (raw leaf position)
// determines where to read sibling hashes from the file.
func (f *Forest) GenerateProofFromPositions(targets []uint64, snap *ForestSnapshot) (Proof, error) {
	if len(targets) == 0 {
		return Proof{}, nil
	}

	forestRows := f.forestRows

	// Build target pairs with both calculated and actual positions.
	// Each calculatePositionAt is independent (read-only), so parallelize.
	pairs := make([]targetPair, len(targets))
	nTargets := len(targets)
	if nTargets < minParallelSize {
		for i, pos := range targets {
			calcPos, err := f.calculatePositionAt(pos, snap)
			if err != nil {
				return Proof{}, fmt.Errorf("calculatePositionAt for pos %d: %w", pos, err)
			}
			pairs[i] = targetPair{calcPos: calcPos, actualPos: pos}
		}
	} else {
		errs := make([]error, numWorkers)
		pipelineParallelDo(func(wIdx, s, e int) {
			for i := s; i < e; i++ {
				calcPos, err := f.calculatePositionAt(targets[i], snap)
				if err != nil {
					errs[wIdx] = fmt.Errorf("calculatePositionAt for pos %d: %w", targets[i], err)
					return
				}
				pairs[i] = targetPair{calcPos: calcPos, actualPos: targets[i]}
			}
		}, nTargets)
		for _, err := range errs {
			if err != nil {
				return Proof{}, err
			}
		}
	}

	proofHashes, err := f.fetchProofHashesPairsAt(pairs, snap)
	if err != nil {
		return Proof{}, err
	}

	// Output targets use calcPos (the compacted positions).
	outTargets := make([]uint64, len(pairs))
	for i, p := range pairs {
		outTargets[i] = p.calcPos
	}
	if forestRows != defaultForestRows {
		outTargets = translatePositions(outTargets, forestRows, defaultForestRows)
	}

	return Proof{
		Targets: outTargets,
		Proof:   proofHashes,
	}, nil
}

// calculatePositionAt computes the logical (compacted) position of a leaf,
// equivalent to calculatePosition but using ReadAt so it is safe for
// concurrent use with Record. It implements the walk-up-then-walk-down
// algorithm: walk up to the root skipping levels where parentH == currentHash
// (move-ups), recording left/right turns for real levels, then walk back
// down using those turns.
func (f *Forest) calculatePositionAt(rawPos uint64, snap *ForestSnapshot) (uint64, error) {
	forestRows := f.forestRows

	currentHash, err := f.readHashForProof(rawPos, snap)
	if err != nil {
		return 0, err
	}

	currentPos := rawPos
	rowsToTop := 0
	leftRightIndicator := uint64(0)
	for !isRootPositionTotalRows(currentPos, snap.numLeaves, forestRows) {
		parentPos := Parent(currentPos, forestRows)
		parentH, err := f.readHashAt(parentPos)
		if err != nil {
			return 0, fmt.Errorf("read parent at %d: %w", parentPos, err)
		}

		if parentH == currentHash {
			// Sibling was deleted — this level doesn't exist in compacted tree.
		} else {
			if isLeftNiece(currentPos) {
				leftRightIndicator <<= 1
			} else {
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
			retPos = RightChild(retPos, forestRows)
		} else {
			retPos = LeftChild(retPos, forestRows)
		}
	}

	return retPos, nil
}




// fetchProofHashesPairsAt generates proof hashes using the two-position scheme.
// calcPos (from calculatePositionAt) determines row ordering and sibling detection.
// actualPos (raw leaf position) determines where to read sibling hashes.
// This mirrors fetchProofHashes but uses ReadAt for concurrent safety.
func (f *Forest) fetchProofHashesPairsAt(pairs []targetPair, snap *ForestSnapshot) ([]Hash, error) {
	if len(pairs) == 0 {
		return nil, nil
	}

	forestRows := f.forestRows
	numLeaves := snap.numLeaves

	// Sort by calculated position to match pollard ordering.
	targets := make([]targetPair, len(pairs))
	copy(targets, pairs)
	slices.SortFunc(targets, func(a, b targetPair) bool {
		return a.calcPos < b.calcPos
	})

	// deTwin using calculated positions, walking up actualPos with ReadAt.
	targets, err := f.deTwinPairsAt(targets, snap)
	if err != nil {
		return nil, err
	}

	proofHashes := make([]Hash, 0, len(targets)*int(TreeRows(numLeaves)+1))
	for row := uint8(0); row <= forestRows; row++ {
		for i := 0; i < len(targets); i++ {
			calcPos := targets[i].calcPos
			actualPos := targets[i].actualPos

			if calcPos > maxPossiblePosAtRow(row, forestRows) {
				continue
			}
			if row != DetectRow(calcPos, forestRows) {
				continue
			}
			if isRootPositionOnRowTotalRows(calcPos, numLeaves, row, forestRows) {
				continue
			}

			// Walk up actual position to handle move-ups.
			actualParentPos := Parent(actualPos, forestRows)
			parentH, err := f.readHashAt(actualParentPos)
			if err != nil {
				return nil, err
			}
			currentHash, err := f.readHashForProof(actualPos, snap)
			if err != nil {
				return nil, err
			}
			for parentH == currentHash {
				actualPos = actualParentPos
				targets[i].actualPos = actualPos
				actualParentPos = Parent(actualPos, forestRows)
				parentH, err = f.readHashAt(actualParentPos)
				if err != nil {
					return nil, err
				}
			}

			// Check if next target is sibling (using calcPos).
			if i+1 < len(targets) && rightSib(calcPos) == targets[i+1].calcPos {
				targets[i].calcPos = Parent(calcPos, forestRows)
				targets[i].actualPos = actualParentPos
				i++ // Skip sibling
				continue
			}

			// Read sibling hash from actual sibling position.
			proofHash, err := f.readHashForProof(sibling(actualPos), snap)
			if err != nil {
				return nil, err
			}
			proofHashes = append(proofHashes, proofHash)
			targets[i].calcPos = Parent(calcPos, forestRows)
			targets[i].actualPos = actualParentPos
		}

		slices.SortFunc(targets, func(a, b targetPair) bool {
			return a.calcPos < b.calcPos
		})
	}

	return proofHashes, nil
}

// deTwinPairsAt removes sibling pairs from targets using calculated positions,
// walking up actualPos with ReadAt for concurrent safety.
func (f *Forest) deTwinPairsAt(targets []targetPair, snap *ForestSnapshot) ([]targetPair, error) {
	for i := 0; i < len(targets)-1; i++ {
		if targets[i].calcPos|1 == targets[i+1].calcPos {
			targets[i].calcPos = Parent(targets[i].calcPos, f.forestRows)

			// Walk up actualPos to find where the node actually is.
			actualPos := targets[i].actualPos
			currentHash, err := f.readHashForProof(actualPos, snap)
			if err != nil {
				return nil, err
			}
			parentPos := Parent(actualPos, f.forestRows)
			parentH, err := f.readHashAt(parentPos)
			if err != nil {
				return nil, err
			}
			for parentH == currentHash {
				actualPos = parentPos
				parentPos = Parent(actualPos, f.forestRows)
				parentH, err = f.readHashAt(parentPos)
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
