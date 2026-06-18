package utreexo

import (
	"sort"
	"testing"

	"github.com/stretchr/testify/require"
)

// newRehashTestForest creates an in-memory forest with the requested row count
// for rehash helper tests.
func newRehashTestForest(t testing.TB, forestRows uint8) *Forest {
	t.Helper()

	dir := t.TempDir()
	f, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil, dir+"/ctrl", dir+"/slots", forestRows, 0)
	require.NoError(t, err)
	return f
}

// simChainAddHashes extracts hashes from simchain additions for Record, which
// takes hashes rather than Leaf values.
func simChainAddHashes(adds []Leaf) []Hash {
	hashes := make([]Hash, len(adds))
	for i, add := range adds {
		hashes[i] = add.Hash
	}
	return hashes
}

// leafPositionsForHashes looks up the current leaf positions for hashes that a
// simchain block is about to delete.
func leafPositionsForHashes(t testing.TB, f *Forest, hashes []Hash) []uint64 {
	t.Helper()

	positions := make([]uint64, len(hashes))
	for i, hash := range hashes {
		packed, found, err := f.positionMap.Get(hash)
		require.NoError(t, err)
		require.True(t, found, "hash %x missing from position map", hash[:8])
		positions[i] = unpackPos(packed)
	}
	return positions
}

// hashesSortedByPosition returns hashes ordered by their matching positions,
// which is the order expected by a proof whose targets are sorted.
func hashesSortedByPosition(hashes []Hash, positions []uint64) []Hash {
	pairs := make([]struct {
		hash Hash
		pos  uint64
	}, len(hashes))
	for i := range hashes {
		pairs[i] = struct {
			hash Hash
			pos  uint64
		}{hash: hashes[i], pos: positions[i]}
	}
	sort.Slice(pairs, func(i, j int) bool { return pairs[i].pos < pairs[j].pos })

	sorted := make([]Hash, len(pairs))
	for i, pair := range pairs {
		sorted[i] = pair.hash
	}
	return sorted
}

// selectDeletionIndexes chooses deletion indexes from a simchain block. When
// siblingPair is true, it picks two deletions that are leaf-row siblings.
func selectDeletionIndexes(t testing.TB, positions []uint64, count int, siblingPair bool) []int {
	t.Helper()

	if count == 0 {
		return nil
	}
	require.GreaterOrEqual(t, len(positions), count)

	if siblingPair {
		posToIndex := make(map[uint64]int, len(positions))
		for i, pos := range positions {
			posToIndex[pos] = i
		}
		for i, pos := range positions {
			if isLeftNiece(pos) {
				if j, ok := posToIndex[rightSib(pos)]; ok {
					return []int{i, j}
				}
			}
		}
		t.Fatalf("no sibling pair in positions %v", positions)
	}

	selected := make([]int, count)
	for i := range selected {
		selected[i] = i
	}
	return selected
}

// subsetByIndexes returns the entries at indexes while preserving the selected
// order.
func subsetByIndexes[T any](values []T, indexes []int) []T {
	selected := make([]T, len(indexes))
	for i, idx := range indexes {
		selected[i] = values[idx]
	}
	return selected
}

func TestProcessAddsParallel(t *testing.T) {
	const forestRows = uint8(16)

	tests := []struct {
		name string
		// duration and seed configure the deterministic simchain block stream.
		duration uint32
		seed     int64
		numAdds  uint32 // additions per simulated block
		prefix   int    // blocks to record and rehash before the tested range
		tail     int    // blocks recorded into the tested append range
		// fromZero makes the final pass rebuild from leaf 0 instead of prefix.
		fromZero   bool
		expectDels bool
	}{
		{
			name:       "full rebuild with simulated deletions",
			duration:   0x03,
			seed:       0x11,
			numAdds:    8,
			tail:       9,
			fromZero:   true,
			expectDels: true,
		},
		{
			name:     "incremental append with simulated blocks",
			duration: 0,
			seed:     0x21,
			numAdds:  5,
			prefix:   3,
			tail:     4,
		},
		{
			name:     "no appended leaves after simulated prefix",
			duration: 0,
			seed:     0x31,
			numAdds:  4,
			prefix:   4,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			sc := newSimChainWithSeed(tt.duration, tt.seed)

			gotForest := newRehashTestForest(t, forestRows)
			require.NoError(t, gotForest.EnterRecordMode())

			wantForest := newRehashTestForest(t, forestRows)
			sawDels := false

			// Build an already-caught-up prefix. Rehashing this range first
			// creates the same starting point as any later incremental pass
			// that starts from prevLeaves.
			var dels []uint64
			for block := 0; block < tt.prefix; block++ {
				adds, _, delHashes := sc.NextBlock(tt.numAdds)
				sawDels = sawDels || len(delHashes) > 0
				_, delPositions, err := gotForest.Record(simChainAddHashes(adds), delHashes)
				require.NoError(t, err, "record prefix block %d", block)
				dels = append(dels, delPositions...)
				require.NoError(t, wantForest.Modify(adds, delHashes, Proof{}), "modify prefix block %d", block)
			}

			prevLeaves := gotForest.NumLeaves
			// RehashAndProve marks each block's deletions before rehashing; this
			// white-box test drives processAddsParallel directly, so it does the
			// same masking setup itself.
			markDeleted(gotForest, dels)
			require.NoError(t, gotForest.processAddsParallel(0, prevLeaves, forestRows, gotForest.deletedLeafPositions))
			gotPrefixRoots, _, err := gotForest.getRoots(prevLeaves, gotForest.deletedLeafPositions)
			require.NoError(t, err)
			require.Equal(t, wantForest.GetRoots(), gotPrefixRoots)

			// Record the tail without rehashing after each block. This is the
			// important case for processAddsParallel: Record can run several
			// blocks ahead, and one later pass must cover the whole appended
			// range [prevLeaves, NumLeaves).
			dels = dels[:0]
			for block := 0; block < tt.tail; block++ {
				adds, _, delHashes := sc.NextBlock(tt.numAdds)
				sawDels = sawDels || len(delHashes) > 0
				_, delPositions, err := gotForest.Record(simChainAddHashes(adds), delHashes)
				require.NoError(t, err, "record tail block %d", block)
				dels = append(dels, delPositions...)
				require.NoError(t, wantForest.Modify(adds, delHashes, Proof{}), "modify tail block %d", block)
			}

			fromLeaves := prevLeaves
			if tt.fromZero {
				fromLeaves = 0
			}
			// fromZero covers crash/reopen-style full regeneration. The other
			// cases cover incremental catch-up from the previously generated
			// leaf count.
			markDeleted(gotForest, dels)
			require.NoError(t, gotForest.processAddsParallel(fromLeaves, gotForest.NumLeaves, forestRows, gotForest.deletedLeafPositions))
			if tt.expectDels {
				require.True(t, sawDels, "simchain case should exercise deletions")
			}

			gotRoots, _, err := gotForest.getRoots(gotForest.NumLeaves, gotForest.deletedLeafPositions)
			require.NoError(t, err)
			require.Equal(t, wantForest.GetRoots(), gotRoots)
		})
	}
}

func TestRehashDeletionsAndCaptureProof(t *testing.T) {
	const forestRows = uint8(16)

	tests := []struct {
		name string
		// duration and seed configure the deterministic simchain block stream.
		duration    uint32
		seed        int64
		numAdds     uint32 // additions per simulated block
		delCount    int    // deletions to select from the candidate block
		siblingPair bool   // require the selected deletions to be leaf siblings
		maxBlocks   int    // maximum blocks to scan for a matching candidate
	}{
		{
			name:      "simulated block with no deletions",
			duration:  0,
			seed:      0x41,
			numAdds:   5,
			maxBlocks: 1,
		},
		{
			name:      "simulated lone deletion",
			duration:  0x03,
			seed:      0x51,
			numAdds:   8,
			delCount:  1,
			maxBlocks: 20,
		},
		{
			name:      "simulated scattered deletions",
			duration:  0x07,
			seed:      0x61,
			numAdds:   16,
			delCount:  4,
			maxBlocks: 30,
		},
		{
			name:        "simulated sibling pair deletion",
			duration:    0x01,
			seed:        0x71,
			numAdds:     32,
			delCount:    2,
			siblingPair: true,
			maxBlocks:   30,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			sc := newSimChainWithSeed(tt.duration, tt.seed)

			gotForest := newRehashTestForest(t, forestRows)
			wantForest := newRehashTestForest(t, forestRows)

			for block := 0; block < tt.maxBlocks; block++ {
				// Advance both forests with simchain blocks until the next
				// block has the deletion shape this table row wants. Blocks
				// that do not match are applied normally so later candidates
				// still come from a realistic chain state.
				adds, _, delHashes := sc.NextBlock(tt.numAdds)
				delPositions := leafPositionsForHashes(t, gotForest, delHashes)

				if len(delHashes) < tt.delCount {
					require.NoError(t, gotForest.Modify(adds, delHashes, Proof{}), "advance got block %d", block)
					require.NoError(t, wantForest.Modify(adds, delHashes, Proof{}), "advance want block %d", block)
					continue
				}

				// The simchain block may contain more deletes than the case
				// needs. Select a deterministic subset so the table can pin
				// lone, scattered, and sibling-pair deletion shapes.
				selected := selectDeletionIndexes(t, delPositions, tt.delCount, tt.siblingPair)
				delHashes = subsetByIndexes(delHashes, selected)
				delPositions = subsetByIndexes(delPositions, selected)

				// The deletion helper assumes this block's adds are already
				// present. Apply the adds first on both forests, then use the
				// normal forest proof path as the expected proof.
				require.NoError(t, gotForest.Modify(adds, nil, Proof{}), "add candidate block")
				require.NoError(t, wantForest.Modify(adds, nil, Proof{}), "add candidate block")

				rootsBefore := gotForest.GetRoots()
				require.Equal(t, wantForest.GetRoots(), rootsBefore)

				// The helper sorts targets by position, so ask wantForest for
				// the expected proof with deletion hashes in that same order.
				sortedDelHashes := hashesSortedByPosition(delHashes, delPositions)
				wantProof, err := wantForest.Prove(sortedDelHashes)
				require.NoError(t, err)

				// Record normally marks these positions before the helper runs.
				// The test calls the helper directly, so mark the bitmap here
				// to exercise the same masking path.
				for _, pos := range delPositions {
					gotForest.deletedLeafPositions.set(pos)
				}

				proof, err := gotForest.rehashDeletionsAndCaptureProof(delPositions, gotForest.NumLeaves, forestRows, gotForest.deletedLeafPositions)
				require.NoError(t, err)
				require.Equal(t, wantProof, proof)

				if len(sortedDelHashes) > 0 {
					_, err = Verify(Stump{Roots: rootsBefore, NumLeaves: gotForest.NumLeaves}, sortedDelHashes, proof)
					require.NoError(t, err)
					require.NoError(t, wantForest.Modify(nil, sortedDelHashes, wantProof))
				}

				gotRoots, _, err := gotForest.getRoots(gotForest.NumLeaves, gotForest.deletedLeafPositions)
				require.NoError(t, err)
				require.Equal(t, wantForest.GetRoots(), gotRoots)
				return
			}

			t.Fatalf("simchain did not produce a matching deletion block within %d blocks", tt.maxBlocks)
		})
	}
}

// TestRehashAndProveRootsMatchModify drives the same add/delete history through
// the normal Modify path and through Record + RehashAndProve, asserting after
// every block that RehashAndProve returns the same roots and a proof of the
// block's deletions that verifies. The reference forest applies each block in
// two steps — adds, then deletions — so the roots captured in between, with the
// adds in and the deletions still present, are exactly the state the proof must
// verify against. Per-block calls exercise the incremental path: each pass only
// rehashes the leaves appended since the previous one. numAdds keeps every add
// rehash past minParallelSize, and the deletion rows cross it once the sim
// chain's spends ramp up, so the worker-pool path runs (and is exercised under
// the race detector).
func TestRehashAndProveRootsMatchModify(t *testing.T) {
	const (
		numAdds  = uint32(8192)
		duration = uint32(0x07)
		seed     = int64(0x07)
		blocks   = 7
	)
	sc := newSimChainWithSeed(duration, seed)

	dir1 := t.TempDir()
	modifyForest, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil, dir1+"/ctrl", dir1+"/slots", 16, 0)
	require.NoError(t, err)

	dir2 := t.TempDir()
	recordForest, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil, dir2+"/ctrl", dir2+"/slots", 16, 0)
	require.NoError(t, err)
	require.NoError(t, recordForest.EnterRecordMode())

	for b := 0; b < blocks; b++ {
		adds, _, delHashes := sc.NextBlock(numAdds)

		// Adds first on the reference forest: the roots captured in between
		// hold this block's adds with its deletions still present, which is
		// the state the proof verifies against. Forest.Modify ignores its
		// proof argument, so an empty proof is fine.
		require.NoError(t, modifyForest.Modify(adds, nil, Proof{}), "block %d", b)
		stump := Stump{Roots: modifyForest.GetRoots(), NumLeaves: modifyForest.NumLeaves}
		require.NoError(t, modifyForest.Modify(nil, delHashes, Proof{}), "block %d", b)

		addHashes := make([]Hash, len(adds))
		for i, add := range adds {
			addHashes[i] = add.Hash
		}
		_, delPositions, err := recordForest.Record(addHashes, delHashes)
		require.NoError(t, err, "block %d", b)

		roots, numLeaves, proof, err := recordForest.RehashAndProve(recordForest.Snapshot(recordForest.NumLeaves), delPositions)
		require.NoError(t, err, "block %d", b)

		require.Equal(t, modifyForest.NumLeaves, numLeaves, "block %d numLeaves", b)
		require.Equal(t, modifyForest.GetRoots(), roots, "block %d roots", b)

		if len(delPositions) == 0 {
			continue
		}

		// RehashAndProve sorts its targets ascending, so the del hashes must
		// be reordered by ascending leaf position to line up with
		// proof.Targets.
		order := make([]int, len(delPositions))
		for i := range order {
			order[i] = i
		}
		sort.Slice(order, func(a, b int) bool { return delPositions[order[a]] < delPositions[order[b]] })
		delByPos := make([]Hash, len(delPositions))
		for i, idx := range order {
			delByPos[i] = delHashes[idx]
		}

		_, err = Verify(stump, delByPos, proof)
		require.NoError(t, err, "block %d proof", b)
	}
}

// TestRehashAndProvePreservesDeletedRootLeaf deletes a leaf that is itself a
// root (a single-leaf tree) through the record pipeline and then undoes the
// block. The masking walk must leave the leaf's hash in its slot — readers
// mask the position through the deleted bitmap, and Undo restores the root
// from the preserved hash, just as it does after a deleteSingle of the same
// leaf.
func TestRehashAndProvePreservesDeletedRootLeaf(t *testing.T) {
	dir := t.TempDir()
	f, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil,
		dir+"/ctrl", dir+"/slots", 16, 0)
	require.NoError(t, err)

	hashes := make([]Hash, 3)
	leaves := make([]Leaf, 3)
	for i := range leaves {
		hashes[i] = testHashFromInt(i)
		leaves[i] = Leaf{Hash: hashes[i]}
	}
	// Three leaves form a two-leaf tree plus a single-leaf tree, so the
	// third leaf's position is a row-0 root.
	require.NoError(t, f.Modify(leaves, nil, Proof{}))
	rootsBefore := f.GetRoots()

	require.NoError(t, f.EnterRecordMode())
	_, delPositions, err := f.Record(nil, hashes[2:3])
	require.NoError(t, err)
	_, _, _, err = f.RehashAndProve(f.Snapshot(f.NumLeaves), delPositions)
	require.NoError(t, err)
	require.NoError(t, f.ExitRecordMode())

	require.NoError(t, f.Undo(nil, Proof{}, hashes[2:3], nil))
	require.Equal(t, rootsBefore, f.GetRoots(),
		"undoing the recorded deletion must restore the root leaf's hash")
}
