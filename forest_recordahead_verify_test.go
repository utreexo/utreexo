package utreexo

import (
	"testing"

	"github.com/stretchr/testify/require"
)

// markDeleted sets the given leaf positions in the forest's deleted bitmap,
// mirroring what each block's RehashAndProve does. White-box tests that drive
// the low-level rehash helpers (or HashAll) directly use it to reproduce the
// masking the real callers set up, since Record no longer marks the bitmap.
func markDeleted(f *Forest, positions []uint64) {
	for _, pos := range positions {
		f.deletedLeafPositions.set(pos)
	}
}

// TestRecordAheadSkew demonstrates whether RehashAndProve(N) reflects block N's
// state or a later block's state when record runs ahead of generate, which is
// exactly the IBD proof pipeline's steady state (record stage runs up to the
// channel buffer depth ahead of the generate stage).
//
// Ground truth per block comes from a separate forest driven by the serial
// Modify path.
func TestRecordAheadSkew(t *testing.T) {
	const (
		numAdds  = uint32(8)
		duration = uint32(0x07)
		seed     = int64(0x07)
		blocks   = 3
	)

	// Ground-truth forest: serial Modify, capture true per-block roots+numLeaves.
	gtChain := newSimChainWithSeed(duration, seed)
	gdir := t.TempDir()
	gt, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil, gdir+"/ctrl", gdir+"/slots", 16, 0)
	require.NoError(t, err)

	type blockState struct {
		numLeaves uint64
		roots     []Hash
		addHashes []Hash
		delHashes []Hash
	}
	truth := make([]blockState, blocks)
	for b := 0; b < blocks; b++ {
		adds, _, delHashes := gtChain.NextBlock(numAdds)
		require.NoError(t, gt.Modify(adds, delHashes, Proof{}), "gt block %d", b)
		truth[b] = blockState{
			numLeaves: gt.NumLeaves,
			roots:     gt.GetRoots(),
			addHashes: simChainAddHashes(adds),
			delHashes: delHashes,
		}
	}

	// Record-ahead forest: record ALL blocks first (mirroring the record stage
	// running ahead), capturing each block's delPositions, then rehash block 0.
	rdir := t.TempDir()
	rf, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil, rdir+"/ctrl", rdir+"/slots", 16, 0)
	require.NoError(t, err)
	require.NoError(t, rf.EnterRecordMode())

	delPositionsByBlock := make([][]uint64, blocks)
	for b := 0; b < blocks; b++ {
		_, delPositions, err := rf.Record(truth[b].addHashes, truth[b].delHashes)
		require.NoError(t, err, "record block %d", b)
		delPositionsByBlock[b] = delPositions
	}

	// generate(0): rehash block 0 AFTER blocks 1 and 2 were recorded, passing
	// block 0's captured leaf count rather than the live (ahead) f.NumLeaves.
	roots0, numLeaves0, _, err := rf.RehashAndProve(rf.Snapshot(truth[0].numLeaves), delPositionsByBlock[0])
	require.NoError(t, err)

	t.Logf("block 0 TRUE  numLeaves=%d roots=%d root(s)", truth[0].numLeaves, len(truth[0].roots))
	t.Logf("block 0 STORED numLeaves=%d roots=%d root(s) (what the pipeline would persist at height 0)", numLeaves0, len(roots0))
	t.Logf("block 2 TRUE  numLeaves=%d", truth[blocks-1].numLeaves)

	require.Equal(t, truth[0].numLeaves, numLeaves0,
		"height 0 stored numLeaves must equal block 0's true cumulative leaf count")
	require.Equal(t, truth[0].roots, roots0,
		"height 0 stored roots must equal block 0's true roots")
}

// TestLockstepNoSkew is the control: strict Record(N) -> RehashAndProve(N)
// alternation, which is the only ordering the existing tests cover.
func TestLockstepNoSkew(t *testing.T) {
	const (
		numAdds  = uint32(8)
		duration = uint32(0x07)
		seed     = int64(0x07)
		blocks   = 3
	)

	gtChain := newSimChainWithSeed(duration, seed)
	gdir := t.TempDir()
	gt, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil, gdir+"/ctrl", gdir+"/slots", 16, 0)
	require.NoError(t, err)

	rdir := t.TempDir()
	rf, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil, rdir+"/ctrl", rdir+"/slots", 16, 0)
	require.NoError(t, err)
	require.NoError(t, rf.EnterRecordMode())

	for b := 0; b < blocks; b++ {
		adds, _, delHashes := gtChain.NextBlock(numAdds)
		require.NoError(t, gt.Modify(adds, delHashes, Proof{}), "gt block %d", b)

		addHashes := simChainAddHashes(adds)
		_, delPositions, err := rf.Record(addHashes, delHashes)
		require.NoError(t, err, "record block %d", b)
		roots, numLeaves, _, err := rf.RehashAndProve(rf.Snapshot(gt.NumLeaves), delPositions)
		require.NoError(t, err, "rehash block %d", b)

		require.Equal(t, gt.NumLeaves, numLeaves, "block %d numLeaves", b)
		require.Equal(t, gt.GetRoots(), roots, "block %d roots", b)
	}
}
