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
			for block := 0; block < tt.prefix; block++ {
				adds, _, delHashes := sc.NextBlock(tt.numAdds)
				sawDels = sawDels || len(delHashes) > 0
				_, _, err := gotForest.Record(simChainAddHashes(adds), delHashes)
				require.NoError(t, err, "record prefix block %d", block)
				require.NoError(t, wantForest.Modify(adds, delHashes, Proof{}), "modify prefix block %d", block)
			}

			prevLeaves := gotForest.NumLeaves
			require.NoError(t, gotForest.processAddsParallel(0, prevLeaves, forestRows))
			gotPrefixRoots, _, err := gotForest.getRoots(prevLeaves)
			require.NoError(t, err)
			require.Equal(t, wantForest.GetRoots(), gotPrefixRoots)

			// Record the tail without rehashing after each block. This is the
			// important case for processAddsParallel: Record can run several
			// blocks ahead, and one later pass must cover the whole appended
			// range [prevLeaves, NumLeaves).
			for block := 0; block < tt.tail; block++ {
				adds, _, delHashes := sc.NextBlock(tt.numAdds)
				sawDels = sawDels || len(delHashes) > 0
				_, _, err := gotForest.Record(simChainAddHashes(adds), delHashes)
				require.NoError(t, err, "record tail block %d", block)
				require.NoError(t, wantForest.Modify(adds, delHashes, Proof{}), "modify tail block %d", block)
			}

			fromLeaves := prevLeaves
			if tt.fromZero {
				fromLeaves = 0
			}
			// fromZero covers crash/reopen-style full regeneration. The other
			// cases cover incremental catch-up from the previously generated
			// leaf count.
			require.NoError(t, gotForest.processAddsParallel(fromLeaves, gotForest.NumLeaves, forestRows))
			if tt.expectDels {
				require.True(t, sawDels, "simchain case should exercise deletions")
			}

			gotRoots, _, err := gotForest.getRoots(gotForest.NumLeaves)
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

				proof, err := gotForest.rehashDeletionsAndCaptureProof(delPositions, gotForest.NumLeaves, forestRows)
				require.NoError(t, err)
				require.Equal(t, wantProof, proof)

				if len(sortedDelHashes) > 0 {
					_, err = Verify(Stump{Roots: rootsBefore, NumLeaves: gotForest.NumLeaves}, sortedDelHashes, proof)
					require.NoError(t, err)
					require.NoError(t, wantForest.Modify(nil, sortedDelHashes, wantProof))
				}

				gotRoots, _, err := gotForest.getRoots(gotForest.NumLeaves)
				require.NoError(t, err)
				require.Equal(t, wantForest.GetRoots(), gotRoots)
				return
			}

			t.Fatalf("simchain did not produce a matching deletion block within %d blocks", tt.maxBlocks)
		})
	}
}
