package utreexo

import (
	"encoding/binary"
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"
)

// walForestFiles holds the in-memory backing files of a WAL-backed forest so
// a test can reopen the same on-disk state, simulating a process restart.
type walForestFiles struct {
	journal         *memFile
	mainFile        *memFile
	delFile         *memFile
	blockCountsFile *memFile
	metaFile        *memFile
}

func newWALForestFiles() *walForestFiles {
	return &walForestFiles{
		journal:         newMemFile(),
		mainFile:        newMemFile(),
		delFile:         newMemFile(),
		blockCountsFile: newMemFile(),
		metaFile:        newMemFile(),
	}
}

// open builds a WAL and a forest over the backing files. Each call uses a
// fresh position-map directory, so reopening rebuilds the position map from
// the leaves like a restart with a consistency-hash mismatch would.
func (wf *walForestFiles) open(t *testing.T) (*wal, *Forest) {
	t.Helper()
	w, err := newWAL(wf.journal, wf.delFile,
		walFile{File: wf.mainFile, EntrySize: 32},
		walFile{File: wf.blockCountsFile, EntrySize: 4},
		walFile{File: wf.metaFile, EntrySize: 32},
	)
	require.NoError(t, err)
	// Release the cachedRWS mmap regions when the test ends; each one
	// reserves a 1 TiB virtual region and the overcommit budget is shared
	// across the whole test process (see wrapMem).
	t.Cleanup(w.Close)

	dir := t.TempDir()
	f, err := newForest(w.Cached(0), w.Cached(1), w.Cached(2), w.Bitmap(),
		dir+"/ctrl", dir+"/slots", 16, 0)
	require.NoError(t, err)
	return w, f
}

// recordBlock runs one block through Record on f and through Modify on ref,
// returning the recorded deletion positions.
func recordBlock(t *testing.T, f, ref *Forest, adds []Leaf, delHashes []Hash) []uint64 {
	t.Helper()
	require.NoError(t, ref.Modify(adds, delHashes, Proof{}))

	addHashes := make([]Hash, len(adds))
	for i, add := range adds {
		addHashes[i] = add.Hash
	}
	_, delPositions, err := f.Record(addHashes, delHashes)
	require.NoError(t, err)
	return delPositions
}

// TestGeneratedLeavesSlotWrites walks the generated-leaves slot through the
// state changes of the record pipeline and checks its value after each one:
// the slot holds NumLeaves exactly when every recorded deletion has been
// masked and every leaf covered by a rehash pass, and zero otherwise.
func TestGeneratedLeavesSlotWrites(t *testing.T) {
	dir := t.TempDir()
	f, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil,
		dir+"/ctrl", dir+"/slots", 16, 0)
	require.NoError(t, err)

	readSlot := func() uint64 {
		t.Helper()
		entry, err := f.metaFile.HashAt(generatedLeavesOffset)
		require.NoError(t, err)
		return binary.LittleEndian.Uint64(entry[:8])
	}

	hashes := make([]Hash, 8)
	leaves := make([]Leaf, 8)
	for i := range hashes {
		hashes[i] = testHashFromInt(i)
		leaves[i] = Leaf{Hash: hashes[i]}
	}

	// Modify maintains interior hashes as it goes, so the slot tracks
	// NumLeaves across it.
	require.NoError(t, f.Modify(leaves[:4], nil, Proof{}))
	require.Equal(t, uint64(4), readSlot())

	require.NoError(t, f.EnterRecordMode())

	// Record leaves interiors unbuilt: the slot must drop to zero and stay
	// there until a rehash pass covers the appended leaves.
	_, _, err = f.Record(hashes[4:6], nil)
	require.NoError(t, err)
	require.Equal(t, uint64(0), readSlot())

	_, _, _, err = f.RehashAndProve(nil)
	require.NoError(t, err)
	require.Equal(t, uint64(6), readSlot())

	// A deletions-only Record leaves NumLeaves unchanged, but its masking
	// walk has not run, so the slot must still drop to zero.
	_, delPositions, err := f.Record(nil, hashes[:1])
	require.NoError(t, err)
	require.Equal(t, uint64(6), f.GetNumLeaves())
	require.Equal(t, uint64(0), readSlot())

	_, _, _, err = f.RehashAndProve(delPositions)
	require.NoError(t, err)
	require.Equal(t, uint64(6), readSlot())

	// Pipelined blocks: with two blocks recorded, the pass covering only the
	// first block's deletions leaves the second's unmasked, so the slot stays
	// zero until the second pass drains the pipeline.
	_, delsA, err := f.Record(hashes[6:7], hashes[1:2])
	require.NoError(t, err)
	_, delsB, err := f.Record(hashes[7:8], hashes[2:3])
	require.NoError(t, err)

	_, _, _, err = f.RehashAndProve(delsA)
	require.NoError(t, err)
	require.Equal(t, uint64(0), readSlot())

	_, _, _, err = f.RehashAndProve(delsB)
	require.NoError(t, err)
	require.Equal(t, uint64(8), readSlot())
}

// TestGeneratedLeavesReopenDrained checks that a flush taken with the record
// pipeline fully caught up seeds lastGeneratedLeaves on reopen, so the next
// RehashAndProve pass covers only leaves appended after the restart, and that
// the roots stay correct across it.
func TestGeneratedLeavesReopenDrained(t *testing.T) {
	sc := newSimChainWithSeed(0x07, 0x07)

	refDir := t.TempDir()
	ref, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil,
		refDir+"/ctrl", refDir+"/slots", 16, 0)
	require.NoError(t, err)

	files := newWALForestFiles()
	w, f := files.open(t)
	require.NoError(t, f.EnterRecordMode())

	for b := 0; b < 5; b++ {
		adds, _, delHashes := sc.NextBlock(64)
		delPositions := recordBlock(t, f, ref, adds, delHashes)
		_, _, _, err := f.RehashAndProve(delPositions)
		require.NoError(t, err, "block %d", b)
	}
	require.NoError(t, w.Flush([32]byte{}))

	_, f2 := files.open(t)
	require.True(t, f2.IsRecordMode())
	require.Equal(t, f2.NumLeaves, f2.lastGeneratedLeaves,
		"a drained flush must seed lastGeneratedLeaves on reopen")

	for b := 0; b < 5; b++ {
		adds, _, delHashes := sc.NextBlock(64)
		delPositions := recordBlock(t, f2, ref, adds, delHashes)
		roots, _, _, err := f2.RehashAndProve(delPositions)
		require.NoError(t, err, "block %d", b)
		require.Equal(t, ref.GetRoots(), roots, "block %d roots", b)
	}
}

// TestGeneratedLeavesReopenUndrained checks that a flush taken with recorded
// blocks whose rehash never ran reopens with lastGeneratedLeaves zero, and
// that the full pass of the next RehashAndProve call rebuilds the correct
// roots from the leaves and the deleted bitmap alone.
func TestGeneratedLeavesReopenUndrained(t *testing.T) {
	sc := newSimChainWithSeed(0x07, 0x07)

	refDir := t.TempDir()
	ref, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil,
		refDir+"/ctrl", refDir+"/slots", 16, 0)
	require.NoError(t, err)

	files := newWALForestFiles()
	w, f := files.open(t)
	require.NoError(t, f.EnterRecordMode())

	sawDels := false
	for b := 0; b < 5; b++ {
		adds, _, delHashes := sc.NextBlock(64)
		delPositions := recordBlock(t, f, ref, adds, delHashes)
		sawDels = sawDels || len(delPositions) > 0
	}
	require.True(t, sawDels, "history must include recorded deletions")
	require.NoError(t, w.Flush([32]byte{}))

	_, f2 := files.open(t)
	require.Zero(t, f2.lastGeneratedLeaves,
		"an undrained flush must not seed lastGeneratedLeaves")

	// One more recorded block whose deletion positions are never passed to
	// a rehash pass, so the deletion count is nonzero going into the heal.
	adds, _, delHashes := sc.NextBlock(64)
	delPositions := recordBlock(t, f2, ref, adds, delHashes)
	require.NotEmpty(t, delPositions)

	// The recorded deletions are in the bitmap but were never passed to a
	// rehash pass. The full pass masks them all at the leaf row — no
	// deletion walk needed — so it must also settle the deletion count:
	// exiting record mode afterwards is legal.
	roots, _, _, err := f2.RehashAndProve(nil)
	require.NoError(t, err)
	require.Equal(t, ref.GetRoots(), roots)

	// The full pass covered every leaf and settled the deletion count, so the
	// forest is caught up and may leave record mode.
	require.Equal(t, f2.NumLeaves, f2.lastGeneratedLeaves)
	require.Zero(t, f2.unmaskedDels)
	require.NoError(t, f2.ExitRecordMode())
}

// TestGeneratedLeavesReopenDelsOnlyBlock pins the case that makes the slot
// more than a saved copy of lastGeneratedLeaves: a deletions-only block
// leaves NumLeaves untouched, so a slot keyed on the leaf count alone would
// still match after a flush and skip the rebuild that the unmasked
// deletions require.
func TestGeneratedLeavesReopenDelsOnlyBlock(t *testing.T) {
	sc := newSimChainWithSeed(0x07, 0x07)

	refDir := t.TempDir()
	ref, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil,
		refDir+"/ctrl", refDir+"/slots", 16, 0)
	require.NoError(t, err)

	files := newWALForestFiles()
	w, f := files.open(t)
	require.NoError(t, f.EnterRecordMode())

	for b := 0; b < 5; b++ {
		adds, _, delHashes := sc.NextBlock(64)
		delPositions := recordBlock(t, f, ref, adds, delHashes)
		_, _, _, err := f.RehashAndProve(delPositions)
		require.NoError(t, err, "block %d", b)
	}

	// One deletions-only block, recorded but not rehashed.
	_, _, delHashes := sc.NextBlock(0)
	require.NotEmpty(t, delHashes, "the simulated block must spend something")
	numLeavesBefore := f.GetNumLeaves()
	delPositions := recordBlock(t, f, ref, nil, delHashes)
	require.NotEmpty(t, delPositions)
	require.NoError(t, w.Flush([32]byte{}))

	_, f2 := files.open(t)
	require.Equal(t, numLeavesBefore, f2.NumLeaves)
	require.Zero(t, f2.lastGeneratedLeaves,
		"unmasked deletions must invalidate the slot even with NumLeaves unchanged")

	roots, _, _, err := f2.RehashAndProve(nil)
	require.NoError(t, err)
	require.Equal(t, ref.GetRoots(), roots)
}

// TestGeneratedLeavesLegacyMetaFile opens a meta file that ends at the
// consistency hash, the layout written before the generated-leaves slot
// existed. The slot must read as absent — falling back to the full rebuild
// pass — while recordMode and numLeaves load intact.
func TestGeneratedLeavesLegacyMetaFile(t *testing.T) {
	sc := newSimChainWithSeed(0x07, 0x07)

	refDir := t.TempDir()
	ref, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil,
		refDir+"/ctrl", refDir+"/slots", 16, 0)
	require.NoError(t, err)

	files := newWALForestFiles()
	w, f := files.open(t)
	require.NoError(t, f.EnterRecordMode())

	for b := 0; b < 5; b++ {
		adds, _, delHashes := sc.NextBlock(64)
		delPositions := recordBlock(t, f, ref, adds, delHashes)
		_, _, _, err := f.RehashAndProve(delPositions)
		require.NoError(t, err, "block %d", b)
	}
	numLeaves := f.GetNumLeaves()
	require.NoError(t, w.Flush([32]byte{}))

	// Truncate the meta file to the legacy 96-byte layout.
	legacyMeta := newMemFile()
	buf := make([]byte, generatedLeavesOffset)
	_, err = files.metaFile.ReadAt(buf, 0)
	require.NoError(t, err)
	_, err = legacyMeta.WriteAt(buf, 0)
	require.NoError(t, err)
	files.metaFile = legacyMeta
	files.journal = newMemFile()

	_, f2 := files.open(t)
	require.Equal(t, numLeaves, f2.NumLeaves,
		"numLeaves must survive a meta file without the generated-leaves slot")
	require.True(t, f2.IsRecordMode())
	require.Zero(t, f2.lastGeneratedLeaves)

	roots, _, _, err := f2.RehashAndProve(nil)
	require.NoError(t, err)
	require.Equal(t, ref.GetRoots(), roots)
}

// TestGeneratedLeavesLegacyMetaFileNormalMode opens a normal-mode database
// whose meta file ends at the consistency hash, the layout written before the
// generated-leaves slot existed, the way an existing database looks right after
// an upgrade. The forest ran entirely on the Modify path, so its interior
// hashes are complete on disk and it must accept the next block straight away.
// The generated-leaves slot reads as absent on reopen, so the forest has to
// recognize the interiors as current from the normal-mode invariant rather than
// from the slot; otherwise the first Modify is rejected as running over stale
// parent hashes even though nothing is stale.
func TestGeneratedLeavesLegacyMetaFileNormalMode(t *testing.T) {
	sc := newSimChainWithSeed(0x07, 0x07)

	refDir := t.TempDir()
	ref, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil,
		refDir+"/ctrl", refDir+"/slots", 16, 0)
	require.NoError(t, err)

	files := newWALForestFiles()
	w, f := files.open(t)

	// Drive the forest entirely through the normal Modify path, which keeps the
	// interior hashes complete at every flush.
	for b := 0; b < 5; b++ {
		adds, _, delHashes := sc.NextBlock(64)
		require.NoError(t, ref.Modify(adds, delHashes, Proof{}), "ref block %d", b)
		require.NoError(t, f.Modify(adds, delHashes, Proof{}), "block %d", b)
	}
	numLeaves := f.GetNumLeaves()
	require.NoError(t, w.Flush([32]byte{}))

	// Truncate the meta file to the legacy 96-byte layout, dropping the
	// generated-leaves slot, as an upgrade of an existing database would see it.
	legacyMeta := newMemFile()
	buf := make([]byte, generatedLeavesOffset)
	_, err = files.metaFile.ReadAt(buf, 0)
	require.NoError(t, err)
	_, err = legacyMeta.WriteAt(buf, 0)
	require.NoError(t, err)
	files.metaFile = legacyMeta
	files.journal = newMemFile()

	_, f2 := files.open(t)
	require.False(t, f2.IsRecordMode(),
		"a normal-mode database must reopen in normal mode")
	require.Equal(t, numLeaves, f2.NumLeaves,
		"numLeaves must survive a meta file without the generated-leaves slot")
	require.Equal(t, f2.NumLeaves, f2.lastGeneratedLeaves,
		"a flushed normal-mode forest has complete interiors, so reopen must "+
			"treat them as current even without the generated-leaves slot")

	// The interiors are complete on disk, so the next block must apply without a
	// manual HashAll and must produce the same roots as the reference.
	adds, _, delHashes := sc.NextBlock(64)
	require.NoError(t, ref.Modify(adds, delHashes, Proof{}))
	require.NoError(t, f2.Modify(adds, delHashes, Proof{}),
		"a reopened normal-mode forest must apply the next block without HashAll")
	require.Equal(t, ref.GetRoots(), f2.GetRoots())
}

// TestGeneratedLeavesReopenNormalMode checks that a forest living entirely on
// the Modify path keeps the slot current, so a reopen seeds
// lastGeneratedLeaves and entering record mode later starts from an
// incremental position.
func TestGeneratedLeavesReopenNormalMode(t *testing.T) {
	sc := newSimChainWithSeed(0x07, 0x07)

	files := newWALForestFiles()
	w, f := files.open(t)

	for b := 0; b < 5; b++ {
		adds, _, delHashes := sc.NextBlock(64)
		require.NoError(t, f.Modify(adds, delHashes, Proof{}), "block %d", b)
	}
	require.NoError(t, w.Flush([32]byte{}))

	_, f2 := files.open(t)
	require.False(t, f2.IsRecordMode())
	require.Equal(t, f2.NumLeaves, f2.lastGeneratedLeaves,
		"a flush on the Modify path must seed lastGeneratedLeaves on reopen")
}

// TestExitRecordModeRequiresCaughtUpInteriors checks that record mode can
// only be left once every recorded block has been through a rehash pass,
// since the normal mutation paths extend existing interior hashes rather
// than rebuild them.
func TestExitRecordModeRequiresCaughtUpInteriors(t *testing.T) {
	dir := t.TempDir()
	f, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil,
		dir+"/ctrl", dir+"/slots", 16, 0)
	require.NoError(t, err)

	// A round trip with nothing recorded exits cleanly.
	require.NoError(t, f.EnterRecordMode())
	require.NoError(t, f.ExitRecordMode())

	hashes := make([]Hash, 4)
	for i := range hashes {
		hashes[i] = testHashFromInt(i)
	}

	// Recorded adds without a rehash pass block the exit.
	require.NoError(t, f.EnterRecordMode())
	_, _, err = f.Record(hashes[:2], nil)
	require.NoError(t, err)
	err = f.ExitRecordMode()
	require.Error(t, err)
	require.Contains(t, err.Error(), "record mode")
	require.True(t, f.IsRecordMode())

	_, _, _, err = f.RehashAndProve(nil)
	require.NoError(t, err)
	require.NoError(t, f.ExitRecordMode())

	// Recorded deletions whose masking walk has not run block the exit even
	// though the leaf count is unchanged.
	require.NoError(t, f.EnterRecordMode())
	_, delPositions, err := f.Record(nil, hashes[:1])
	require.NoError(t, err)
	err = f.ExitRecordMode()
	require.Error(t, err)
	require.Contains(t, err.Error(), "masking walk")

	_, _, _, err = f.RehashAndProve(delPositions)
	require.NoError(t, err)
	require.NoError(t, f.ExitRecordMode())

	// The Modify path runs again once the exit succeeds.
	require.NoError(t, f.Modify([]Leaf{{Hash: hashes[2]}}, nil, Proof{}))
}

// failingForestFile wraps a forestFile and returns an injected error from any
// read at failOff, letting a test force a read fault at a chosen leaf. failOff
// is negative when disabled.
type failingForestFile struct {
	inner   forestFile
	failOff int64
}

func (ff *failingForestFile) ReadAt(p []byte, off int64) (int, error) {
	if ff.failOff >= 0 && off == ff.failOff {
		return 0, fmt.Errorf("injected read fault at offset %d", off)
	}
	return ff.inner.ReadAt(p, off)
}

func (ff *failingForestFile) WriteAt(p []byte, off int64) (int, error) {
	return ff.inner.WriteAt(p, off)
}

func (ff *failingForestFile) HashAt(off int64) ([32]byte, error) {
	if ff.failOff >= 0 && off == ff.failOff {
		return [32]byte{}, fmt.Errorf("injected read fault at offset %d", off)
	}
	return ff.inner.HashAt(off)
}

// TestHashAllRestoresNumLeavesOnFailure drives HashAll into a read fault partway
// through its rebuild and checks that NumLeaves is restored to the real leaf
// count. The leaves and the deleted bitmap still describe every leaf, so a
// retry rebuilds the correct roots rather than truncating the forest. The
// history comes from a sim chain so the forest spans several trees and holds
// recorded deletions, which the rebuild masks at the leaf row.
func TestHashAllRestoresNumLeavesOnFailure(t *testing.T) {
	sc := newSimChainWithSeed(0x07, 0x07)

	// Reference forest built through the normal Modify path.
	refDir := t.TempDir()
	ref, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil,
		refDir+"/ctrl", refDir+"/slots", 16, 0)
	require.NoError(t, err)

	// Record forest whose main file can be made to fail a read on demand.
	mainFile := &failingForestFile{inner: newMemFile(), failOff: -1}
	mainCached, err := newCachedRWS(mainFile, 32, 0, 0)
	require.NoError(t, err)
	t.Cleanup(mainCached.Close)

	dir := t.TempDir()
	f, err := newForest(mainCached, memCached(t, 4), memCached(t, 32), nil,
		dir+"/ctrl", dir+"/slots", 16, 0)
	require.NoError(t, err)
	require.NoError(t, f.EnterRecordMode())

	sawDels := false
	for b := 0; b < 5; b++ {
		adds, _, delHashes := sc.NextBlock(64)
		delPositions := recordBlock(t, f, ref, adds, delHashes)
		sawDels = sawDels || len(delPositions) > 0
	}
	require.True(t, sawDels, "history must include recorded deletions")

	totalLeaves := f.GetNumLeaves()

	// Flush the main file so the rebuild reads leaves from the underlying file,
	// where the fault is injected. Fault the first non-deleted leaf at or past
	// the midpoint (a deleted leaf is masked without a read), so reading it
	// fails partway through HashAll, after earlier leaves have advanced
	// NumLeaves.
	require.NoError(t, f.file.Flush())
	failPos := totalLeaves / 2
	for failPos < totalLeaves && f.deletedLeafPositions.isSet(failPos) {
		failPos++
	}
	require.Less(t, failPos, totalLeaves, "need a non-deleted leaf to fault")
	mainFile.failOff = f.posToFileOffset(failPos)

	require.Error(t, f.HashAll(), "the injected fault must fail HashAll")
	require.Equal(t, totalLeaves, f.GetNumLeaves(),
		"a failed HashAll must restore NumLeaves to the real leaf count")
	require.True(t, f.IsRecordMode(),
		"a failed HashAll leaves the forest in record mode")

	// With the fault cleared, a retry rebuilds every leaf from the leaf row and
	// the deleted bitmap, matching the reference roots, proving no leaf was
	// truncated or overwritten.
	mainFile.failOff = -1
	require.NoError(t, f.HashAll())
	require.Equal(t, ref.GetRoots(), f.GetRoots())
}
