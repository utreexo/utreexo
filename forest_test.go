package utreexo

import (
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"
	"reflect"
	"strings"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"
)

// testHashFromInt creates a deterministic hash from an integer for testing.
func testHashFromInt(n int) Hash {
	var buf [8]byte
	binary.BigEndian.PutUint64(buf[:], uint64(n))
	return sha256.Sum256(buf[:])
}

// memFile is an in-memory implementation of io.ReadWriteSeeker for testing.
// mu protects concurrent ReadAt/WriteAt calls (which are safe on os.File
// at disjoint offsets but race on a []byte slice).
type memFile struct {
	mu     sync.RWMutex
	data   []byte
	offset int64
}

func newMemFile() *memFile {
	return &memFile{data: make([]byte, 0)}
}

func (m *memFile) Read(p []byte) (n int, err error) {
	if m.offset >= int64(len(m.data)) {
		// Extend with zeros for reads beyond current size
		needed := m.offset + int64(len(p)) - int64(len(m.data))
		if needed > 0 {
			m.data = append(m.data, make([]byte, needed)...)
		}
	}
	n = copy(p, m.data[m.offset:])
	m.offset += int64(n)
	return n, nil
}

func (m *memFile) Write(p []byte) (n int, err error) {
	// Extend if necessary
	needed := m.offset + int64(len(p)) - int64(len(m.data))
	if needed > 0 {
		m.data = append(m.data, make([]byte, needed)...)
	}
	n = copy(m.data[m.offset:], p)
	m.offset += int64(n)
	return n, nil
}

func (m *memFile) Seek(offset int64, whence int) (int64, error) {
	switch whence {
	case 0: // io.SeekStart
		m.offset = offset
	case 1: // io.SeekCurrent
		m.offset += offset
	case 2: // io.SeekEnd
		m.offset = int64(len(m.data)) + offset
	}
	return m.offset, nil
}

func (m *memFile) ReadAt(p []byte, off int64) (int, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()
	if off >= int64(len(m.data)) {
		return 0, io.EOF
	}
	n := copy(p, m.data[off:])
	if n < len(p) {
		return n, io.EOF
	}
	return n, nil
}

func (m *memFile) WriteAt(p []byte, off int64) (int, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	needed := off + int64(len(p)) - int64(len(m.data))
	if needed > 0 {
		m.data = append(m.data, make([]byte, needed)...)
	}
	n := copy(m.data[off:], p)
	return n, nil
}

func (m *memFile) Truncate(size int64) error {
	if size < int64(len(m.data)) {
		m.data = m.data[:size]
	}
	if m.offset > size {
		m.offset = size
	}
	return nil
}

// sameHashes checks if two slices contain the same hashes regardless of order.
func sameHashes(a, b []Hash) (same bool, onlyInA, onlyInB []Hash) {
	counts := make(map[Hash]int)
	for _, h := range a {
		counts[h]++
	}
	for _, h := range b {
		counts[h]--
	}
	for h, count := range counts {
		if count > 0 {
			for i := 0; i < count; i++ {
				onlyInA = append(onlyInA, h)
			}
		} else if count < 0 {
			for i := 0; i < -count; i++ {
				onlyInB = append(onlyInB, h)
			}
		}
	}
	same = len(onlyInA) == 0 && len(onlyInB) == 0
	return
}

// compareRoots compares Forest and Pollard roots, failing the test if they differ.
func compareRoots(t *testing.T, forest *Forest, pollard Pollard, context string) {
	t.Helper()

	forestRoots := forest.GetRoots()
	pollardRoots := pollard.GetRoots()

	if len(forestRoots) != len(pollardRoots) {
		t.Fatalf("%s: root count mismatch: forest=%d, pollard=%d",
			context, len(forestRoots), len(pollardRoots))
	}

	for i := range forestRoots {
		if forestRoots[i] != pollardRoots[i] {
			t.Errorf("%s: root %d mismatch:\n  forest:  %x\n  pollard: %x",
				context, i, forestRoots[i][:8], pollardRoots[i][:8])
		}
	}
}

// newTestForest creates a Forest for testing with temp files for the swiss table.
func newTestForest(t *testing.T, forestRows uint8) *Forest {
	t.Helper()
	tmpDir := t.TempDir()
	forest, err := newForest(
		newMemFile(), newMemFile(), newMemFile(), nil,
		tmpDir+"/ctrl", tmpDir+"/slots",
		forestRows, 0,
	)
	require.NoError(t, err)
	return forest
}

// TestForestString tests the ToString interface implementation.
func TestForestString(t *testing.T) {
	// Use small forestRows for visualization
	forest := newTestForest(t, 3)

	// Add 4 leaves
	for i := 0; i < 4; i++ {
		hash := testHashFromInt(i + 1)
		err := forest.add(hash, 0)
		if err != nil {
			t.Fatalf("Add %d: %v", i, err)
		}
	}

	// Test that String() doesn't panic and returns non-empty
	s := String(forest)
	if s == "" {
		t.Error("String() returned empty string")
	}
	t.Logf("Forest visualization:\n%s", s)
}

// TestForestSanityCheck tests that sanityCheck catches inconsistencies.
func TestForestSanityCheck(t *testing.T) {
	// setupForest creates a forest with 4 leaves for each subtest.
	setupForest := func(t *testing.T) (*Forest, []Hash) {
		t.Helper()
		forest := newTestForest(t, 10)
		hashes := make([]Hash, 4)
		for i := range 4 {
			hashes[i] = testHashFromInt(i + 1)
			if err := forest.add(hashes[i], 0); err != nil {
				t.Fatalf("add %d: %v", i, err)
			}
		}
		return forest, hashes
	}

	tests := []struct {
		name    string
		corrupt func(t *testing.T, f *Forest, hashes []Hash)
		wantErr bool
		errStr  string // if non-empty, error must contain this substring
	}{
		{
			name:    "valid forest passes",
			corrupt: func(t *testing.T, f *Forest, hashes []Hash) {},
			wantErr: false,
		},
		{
			name: "extra positionMap entry detected",
			corrupt: func(t *testing.T, f *Forest, hashes []Hash) {
				wrongHash := testHashFromInt(999)
				require.NoError(t, f.positionMap.Set(wrongHash, packPosIndex(0, 0)))
			},
			wantErr: true,
		},
		{
			name: "corrupted file leaf detected",
			corrupt: func(t *testing.T, f *Forest, hashes []Hash) {
				wrongHash := testHashFromInt(999)
				require.NoError(t, f.writeHash(0, wrongHash))
			},
			wantErr: true,
		},
		{
			name: "corrupted root detected",
			corrupt: func(t *testing.T, f *Forest, hashes []Hash) {
				wrongHash := testHashFromInt(999)
				rootPositions := RootPositions(f.NumLeaves, f.forestRows)
				if len(rootPositions) == 0 {
					t.Skip("no roots")
				}
				require.NoError(t, f.writeHash(rootPositions[0], wrongHash))
			},
			wantErr: true,
			errStr:  "invalid parent",
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			forest, hashes := setupForest(t)
			tc.corrupt(t, forest, hashes)

			err := forest.sanityCheck()
			if tc.wantErr {
				require.Error(t, err, "sanityCheck should have failed")
				if tc.errStr != "" {
					require.Contains(t, err.Error(), tc.errStr)
				}
			} else {
				require.NoError(t, err, "sanityCheck failed on valid forest")
			}
		})
	}
}

// sanityCheck checks for inconsistencies in the forest.
// This implements the UtreexoTest interface.
func (f *Forest) sanityCheck() error {
	// Check 0: Verify positionMap entry count matches expected
	// positionMap should have exactly NumLeaves
	expectedPosMapCount := f.NumLeaves
	actualPosMapCount := f.positionMap.Count()
	if actualPosMapCount != expectedPosMapCount {
		return fmt.Errorf("positionMap count mismatch: expected %d, got %d",
			expectedPosMapCount, actualPosMapCount)
	}

	// Check 0.5: Verify deletedLeafPositions bitmap is consistent with positionMap.
	// Every position marked deleted must be a valid leaf in positionMap, and the
	// number of deleted + live leaves must equal NumLeaves.
	deletedCount := uint64(f.deletedLeafPositions.count())
	liveCount := uint64(0)
	f.positionMap.ForEach(func(packed uint64) {
		pos := unpackPos(packed)
		if !f.deletedLeafPositions.isSet(pos) {
			liveCount++
		}
	})
	if deletedCount+liveCount != f.NumLeaves {
		return fmt.Errorf("deletedLeafPositions mismatch: %d deleted + %d live = %d, expected NumLeaves %d",
			deletedCount, liveCount, deletedCount+liveCount, f.NumLeaves)
	}

	// Cache file reads - many paths share ancestors
	readCache := make(map[uint64]Hash)
	cachedRead := func(pos uint64) (Hash, error) {
		if h, ok := readCache[pos]; ok {
			return h, nil
		}
		h, err := f.readHash(pos)
		if err != nil {
			return empty, err
		}
		readCache[pos] = h
		return h, nil
	}

	// Track which parent positions we've already verified
	verified := make(map[uint64]bool)

	// Collect positions to verify from positionMap
	var positions []uint64
	f.positionMap.ForEach(func(packed uint64) {
		pos := unpackPos(packed)

		// Skip deleted positions
		if f.deletedLeafPositions.isSet(pos) {
			return
		}
		positions = append(positions, pos)
	})

	for _, pos := range positions {
		// Check 1: Verify positionMap entry matches file contents
		hash, err := cachedRead(pos)
		if err != nil {
			return fmt.Errorf("positionMap sanity: failed to read pos %d: %w", pos, err)
		}
		// Verify the hash is in positionMap
		_, found, err := f.positionMap.Get(hash)
		if err != nil {
			return fmt.Errorf("positionMap sanity: Get error for pos %d: %w", pos, err)
		}
		if !found {
			return fmt.Errorf("positionMap sanity: hash at pos %d not found in map", pos)
		}

		// Check 2: Verify path to root (skip already-verified parents)
		currentPos := pos
		for !isRootPositionTotalRows(currentPos, f.NumLeaves, f.forestRows) {
			parentPos := Parent(currentPos, f.forestRows)
			if verified[parentPos] {
				break // already verified this path to root
			}

			gotParent, err := cachedRead(parentPos)
			if err != nil {
				return fmt.Errorf("verifyPathToRoot: read parent at %d: %w", parentPos, err)
			}

			leftPos := LeftChild(parentPos, f.forestRows)
			rightPos := RightChild(parentPos, f.forestRows)

			leftHash, err := cachedRead(leftPos)
			if err != nil {
				return fmt.Errorf("verifyPathToRoot: read left at %d: %w", leftPos, err)
			}
			rightHash, err := cachedRead(rightPos)
			if err != nil {
				return fmt.Errorf("verifyPathToRoot: read right at %d: %w", rightPos, err)
			}

			// Parent must be one of:
			// 1. parentHash(left, right) - normal case
			// 2. left child - right was deleted, left moved up
			// 3. right child - left was deleted, right moved up
			// 4. empty - both children deleted
			expectedParent := parentHash(leftHash, rightHash)

			validParent := gotParent == expectedParent ||
				gotParent == leftHash ||
				gotParent == rightHash ||
				gotParent == empty

			if !validParent {
				return fmt.Errorf("invalid parent at pos %d: got %x, expected parentHash(%x, %x)=%x or one of children",
					parentPos, gotParent[:8], leftHash[:8], rightHash[:8], expectedParent[:8])
			}

			verified[parentPos] = true
			currentPos = parentPos
		}
	}

	return nil
}

// nodeMapToString implements the UtreexoTest interface.
func (f *Forest) nodeMapToString() string {
	return f.positionMapToString()
}

// positionMapToString returns the position map as a string.
// Filters out deleted positions and positions >= NumLeaves.
func (f *Forest) positionMapToString() string {
	var sb strings.Builder
	idx := 0
	f.positionMap.ForEach(func(packed uint64) {
		pos := unpackPos(packed)

		// Skip positions >= NumLeaves (undone additions)
		if pos >= f.NumLeaves {
			return
		}
		// Skip deleted positions
		if f.deletedLeafPositions.isSet(pos) {
			return
		}
		// Read hash from file
		hash, err := f.readHash(pos)
		if err != nil {
			return
		}
		if idx != 0 {
			sb.WriteString("\n")
		}
		fmt.Fprintf(&sb, "hash:%s, pos:%d", hex.EncodeToString(hash[:8]), pos)
		idx++
	})
	return sb.String()
}

// rootToString returns the roots as a string.
// This implements the UtreexoTest interface.
func (f *Forest) rootToString() string {
	roots := f.GetRoots()
	return printHashes(roots)
}

func FuzzForestChain(f *testing.F) {
	var tests = []struct {
		numAdds  uint32
		duration uint32
		seed     int64
	}{
		{3, 0x07, 0x07},
	}
	for _, test := range tests {
		f.Add(test.numAdds, test.duration, test.seed)
	}

	f.Fuzz(func(t *testing.T, numAdds, duration uint32, seed int64) {
		t.Parallel()

		// simulate blocks with simchain
		sc := newSimChainWithSeed(duration, seed)

		memFile := newMemFile()
		tmpDir := t.TempDir()
		forest, err := newForest(memFile, newMemFile(), newMemFile(), nil, tmpDir+"/ctrl", tmpDir+"/slots", 16, 0)
		if err != nil {
			t.Fatal(err)
		}
		pollard := NewAccumulator()

		for b := 0; b <= 100; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)

			// Get proof from pollard
			proof, err := pollard.Prove(delHashes)
			if err != nil {
				t.Fatal(err)
			}

			// For forest, generate its own proof with its internal positions
			forestProof, err := forest.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzForestChain fail at block %d. Couldn't prove\n%s\nError: %v",
					b, printHashes(delHashes), err)
			}

			// Check if proofs match
			err = forestProof.checkEqualProof(proof)
			if err != nil {
				same, onlyInForest, onlyInPollard := sameHashes(forestProof.Proof, proof.Proof)
				pollardProofPositions, _ := ProofPositions(proof.Targets, pollard.GetNumLeaves(), TreeRows(pollard.GetNumLeaves()))
				t.Fatalf("Block %d: Proofs differ (same hashes: %v).\ndelHashes: %s\nforest proof: %s\npollard proof: %s\npollard proof positions: %v\n"+
					"only in forest: %s\nonly in pollard: %s\nerr: %v\npollard:\n%s\nforest:\n%s",
					b, same, printHashes(delHashes), forestProof.String(),
					proof.String(), pollardProofPositions,
					printHashes(onlyInForest), printHashes(onlyInPollard), err,
					pollard.String(), forest.String())
			}

			// Modify both - forest uses its own proof, pollard uses its proof
			err = forest.Modify(adds, delHashes, forestProof)
			if err != nil {
				t.Fatalf("FuzzForestChain fail at block %d. Forest Modify Error: %v", b, err)
			}

			err = pollard.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatal(err)
			}

			// Compare roots - this is the key correctness property
			pollardRoots := pollard.GetRoots()
			forestRoots := forest.GetRoots()
			if !reflect.DeepEqual(pollardRoots, forestRoots) {
				t.Fatalf("Roots differ at block %d. expected:\n%s\nbut got:\n%s\npollard:\n%s\nforest:\n%s\n",
					b, printHashes(pollardRoots), printHashes(forestRoots),
					pollard.String(), forest.String())
			}

			// Sanity check forest
			err = forest.sanityCheck()
			if err != nil {
				t.Fatalf("block %v sanityCheck failed: %v\npollard:\n%s\nforest:\n%s\n",
					b, err, pollard.String(), forest.String())
			}
		}
	})
}

// FuzzForestRecord tests that Record + HashAll produces the same result as Modify.
func FuzzForestRecord(f *testing.F) {
	var tests = []struct {
		numAdds  uint32
		duration uint32
		seed     int64
	}{
		{3, 0x07, 0x07},
	}
	for _, test := range tests {
		f.Add(test.numAdds, test.duration, test.seed)
	}

	f.Fuzz(func(t *testing.T, numAdds, duration uint32, seed int64) {
		t.Parallel()

		sc := newSimChainWithSeed(duration, seed)

		// Forest using normal Modify
		tmpDir1 := t.TempDir()
		modifyForest, err := newForest(newMemFile(), newMemFile(), newMemFile(), nil, tmpDir1+"/ctrl", tmpDir1+"/slots", 16, 0)
		if err != nil {
			t.Fatal(err)
		}

		// Forest using Record + HashAll
		tmpDir2 := t.TempDir()
		recordForest, err := newForest(newMemFile(), newMemFile(), newMemFile(), nil, tmpDir2+"/ctrl", tmpDir2+"/slots", 16, 0)
		if err != nil {
			t.Fatal(err)
		}

		// Process all blocks with both approaches
		for b := 0; b <= 100; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)

			// Modify forest needs proof for deletions
			proof, err := modifyForest.Prove(delHashes)
			if err != nil {
				t.Fatalf("block %d: Prove error: %v", b, err)
			}

			err = modifyForest.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("block %d: Modify error: %v", b, err)
			}

			// Record forest just records without hashing
			addHashes := make([]Hash, len(adds))
			for i, add := range adds {
				addHashes[i] = add.Hash
			}
			_, _, err = recordForest.Record(addHashes, delHashes)
			if err != nil {
				t.Fatalf("block %d: Record error: %v", b, err)
			}
		}

		// Now hash all for the record forest
		err = recordForest.HashAll()
		if err != nil {
			t.Fatalf("HashAll error: %v", err)
		}

		// Compare roots
		modifyRoots := modifyForest.GetRoots()
		recordRoots := recordForest.GetRoots()
		require.Equal(t, modifyRoots, recordRoots, "roots should match after Record+HashAll vs Modify")

		err = recordForest.sanityCheck()
		if err != nil {
			t.Fatalf("HashAll error: %v", err)
		}
	})
}

// FuzzForestGenerateRoots tests that Record + Snapshot + GenerateRoots produces
// the same roots as Modify, and that GenerateProof produces valid proofs.
//
// Proof verification requires the tree state BEFORE the deletions being proved.
// So we process blocks 0..N-1, snapshot, GenerateRoots, then prove block N's
// deletions against the block N-1 snapshot.
func FuzzForestGenerateRoots(f *testing.F) {
	var tests = []struct {
		numAdds  uint32
		duration uint32
		seed     int64
	}{
		{3, 0x07, 0x07},
	}
	for _, test := range tests {
		f.Add(test.numAdds, test.duration, test.seed)
	}

	f.Fuzz(func(t *testing.T, numAdds, duration uint32, seed int64) {
		t.Parallel()

		// Cap numAdds to keep test runtime reasonable.
		if numAdds > 1000 {
			numAdds = numAdds%1000 + 1
		}

		sc := newSimChainWithSeed(duration, seed)

		// Compute forestRows large enough for 101 blocks of numAdds leaves.
		maxLeaves := uint64(numAdds) * 101
		forestRows := TreeRows(maxLeaves + 1)
		if forestRows < 16 {
			forestRows = 16
		}

		// Forest using normal Modify (reference)
		tmpDir1 := t.TempDir()
		modifyForest, err := newForest(newMemFile(), newMemFile(), newMemFile(), nil, tmpDir1+"/ctrl", tmpDir1+"/slots", forestRows, 0)
		if err != nil {
			t.Fatal(err)
		}

		// Forest using Record + GenerateRoots
		tmpDir2 := t.TempDir()
		recordForest, err := newForest(newMemFile(), newMemFile(), newMemFile(), nil, tmpDir2+"/ctrl", tmpDir2+"/slots", forestRows, 0)
		if err != nil {
			t.Fatal(err)
		}

		// Process blocks 0..100, calling GenerateRoots per-block to exercise
		// both the full-scan (first call) and incremental paths.
		for b := 0; b <= 100; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)

			proof, err := modifyForest.Prove(delHashes)
			if err != nil {
				t.Fatalf("block %d: Prove error: %v", b, err)
			}

			// Snapshot before Record to capture pre-block state.
			snap := recordForest.Snapshot()

			addHashes := make([]Hash, len(adds))
			for i, add := range adds {
				addHashes[i] = add.Hash
			}
			_, _, err = recordForest.Record(addHashes, delHashes)
			if err != nil {
				t.Fatalf("block %d: Record error: %v", b, err)
			}

			// GenerateRoots should match Modify roots (pre-block state).
			genRoots, genNumLeaves, err := recordForest.GenerateRoots(snap)
			if err != nil {
				t.Fatalf("block %d: GenerateRoots error: %v", b, err)
			}

			modifyRoots := modifyForest.GetRoots()
			require.Equal(t, modifyRoots, genRoots,
				"block %d: GenerateRoots should match Modify roots", b)
			require.Equal(t, modifyForest.NumLeaves, genNumLeaves,
				"block %d: numLeaves mismatch", b)

			// Prove this block's deletions against pre-block snapshot.
			if len(delHashes) > 0 {
				genProof, err := recordForest.GenerateProof(snap, delHashes)
				if err != nil {
					t.Fatalf("block %d: GenerateProof error: %v", b, err)
				}

				stump := Stump{Roots: genRoots, NumLeaves: genNumLeaves}
				_, err = Verify(stump, delHashes, genProof)
				if err != nil {
					t.Fatalf("block %d: GenerateProof verification failed: %v", b, err)
				}
			}

			recordForest.ReleaseSnapshot(snap)

			err = modifyForest.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("block %d: Modify error: %v", b, err)
			}
		}
	})
}

// TestGenerateRootsSmall is a focused test for GenerateRoots intermediate hashes.
func TestGenerateRootsSmall(t *testing.T) {
	// Reference: Modify forest
	modForest := newTestForest(t, 10)
	// Record forest
	recForest := newTestForest(t, 10)

	pollard := NewAccumulator()

	// Add 4 leaves
	h := [4]Hash{testHashFromInt(1), testHashFromInt(2), testHashFromInt(3), testHashFromInt(4)}
	adds := []Leaf{{Hash: h[0]}, {Hash: h[1]}, {Hash: h[2]}, {Hash: h[3]}}

	require.NoError(t, pollard.Modify(adds, nil, Proof{}))
	require.NoError(t, modForest.Modify(adds, nil, Proof{}))
	_, _, err := recForest.Record([]Hash{h[0], h[1], h[2], h[3]}, nil)
	require.NoError(t, err)

	// Delete leaf 1 (sibling of leaf 0)
	delHashes := []Hash{h[1]}
	proof, err := pollard.Prove(delHashes)
	require.NoError(t, err)
	require.NoError(t, pollard.Modify(nil, delHashes, proof))

	modProof, err := modForest.Prove(delHashes)
	require.NoError(t, err)
	require.NoError(t, modForest.Modify(nil, delHashes, modProof))
	_, _, err = recForest.Record(nil, delHashes)
	require.NoError(t, err)

	// Take snapshot and GenerateRoots
	snap := recForest.Snapshot()
	defer recForest.ReleaseSnapshot(snap)

	genRoots, genNL, err := recForest.GenerateRoots(snap)
	require.NoError(t, err)

	modRoots := modForest.GetRoots()
	require.Equal(t, modForest.NumLeaves, genNL)
	require.Equal(t, modRoots, genRoots, "roots must match")

	// Prove leaf 0 (whose sibling h[1] was deleted). h[0] is still
	// in the tree, so the proof should verify against post-deletion roots.
	genProof, err := recForest.GenerateProof(snap, []Hash{h[0]})
	require.NoError(t, err)

	stump := Stump{Roots: genRoots, NumLeaves: genNL}
	_, err = Verify(stump, []Hash{h[0]}, genProof)
	require.NoError(t, err, "GenerateProof should produce a valid proof")
}

// FuzzForestGenerateRootsCOW tests that the COW bitmap correctly preserves
// the snapshot state while the writer continues to advance.
func FuzzForestGenerateRootsCOW(f *testing.F) {
	var tests = []struct {
		numAdds  uint32
		duration uint32
		seed     int64
	}{
		{3, 0x07, 0x07},
	}
	for _, test := range tests {
		f.Add(test.numAdds, test.duration, test.seed)
	}

	f.Fuzz(func(t *testing.T, numAdds, duration uint32, seed int64) {
		t.Parallel()

		// Cap numAdds to keep test runtime reasonable.
		if numAdds > 1000 {
			numAdds = numAdds%1000 + 1
		}

		sc := newSimChainWithSeed(duration, seed)

		// Compute forestRows large enough for 100 blocks of numAdds leaves.
		maxLeaves := uint64(numAdds) * 100
		forestRows := TreeRows(maxLeaves + 1)
		if forestRows < 16 {
			forestRows = 16
		}

		// Reference forest using Modify
		tmpDir1 := t.TempDir()
		modifyForest, err := newForest(newMemFile(), newMemFile(), newMemFile(), nil, tmpDir1+"/ctrl", tmpDir1+"/slots", forestRows, 0)
		if err != nil {
			t.Fatal(err)
		}

		// Record forest
		tmpDir2 := t.TempDir()
		recordForest, err := newForest(newMemFile(), newMemFile(), newMemFile(), nil, tmpDir2+"/ctrl", tmpDir2+"/slots", forestRows, 0)
		if err != nil {
			t.Fatal(err)
		}

		// Process 50 blocks on both.
		for b := 0; b < 50; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)

			proof, err := modifyForest.Prove(delHashes)
			if err != nil {
				t.Fatalf("block %d: Prove error: %v", b, err)
			}
			err = modifyForest.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("block %d: Modify error: %v", b, err)
			}

			addHashes := make([]Hash, len(adds))
			for i, add := range adds {
				addHashes[i] = add.Hash
			}
			_, _, err = recordForest.Record(addHashes, delHashes)
			if err != nil {
				t.Fatalf("block %d: Record error: %v", b, err)
			}
		}

		// Snapshot at block 50.
		snap := recordForest.Snapshot()

		// Writer continues for 50 more blocks AFTER the snapshot.
		for b := 50; b < 100; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)
			addHashes := make([]Hash, len(adds))
			for i, add := range adds {
				addHashes[i] = add.Hash
			}
			_, _, err = recordForest.Record(addHashes, delHashes)
			if err != nil {
				t.Fatalf("block %d: Record error: %v", b, err)
			}
		}

		// GenerateRoots on the snapshot should still match the Modify forest at block 50.
		genRoots, genNumLeaves, err := recordForest.GenerateRoots(snap)
		if err != nil {
			t.Fatalf("GenerateRoots error: %v", err)
		}

		recordForest.ReleaseSnapshot(snap)

		if genNumLeaves != modifyForest.NumLeaves {
			t.Fatalf("numLeaves mismatch: GenerateRoots=%d, Modify=%d",
				genNumLeaves, modifyForest.NumLeaves)
		}

		modifyRoots := modifyForest.GetRoots()
		require.Equal(t, modifyRoots, genRoots,
			"GenerateRoots at snapshot should match Modify roots at block 50, even after writer advanced to block 100")
	})
}

// FuzzTreeBuilding tests that the trees built from adding empty hashes for deleted leaves
// have the same roots as the ones that added the actual value of the leaves and then deleted
// them.
func FuzzTreeBuilding(f *testing.F) {
	var tests = []struct {
		numAdds  uint32
		duration uint32
		seed     int64
	}{
		{3, 0x07, 0x07},
	}
	for _, test := range tests {
		f.Add(test.numAdds, test.duration, test.seed)
	}

	f.Fuzz(func(t *testing.T, numAdds, duration uint32, seed int64) {
		t.Parallel()

		// simulate blocks with simchain
		sc := newSimChainWithSeed(duration, seed)

		m := NewAccumulator()

		blocks := uint32(100)
		allAdds := make([]Leaf, 0, numAdds*blocks)
		allDels := make(map[Hash]struct{}, numAdds*blocks)

		for b := uint32(0); b <= blocks; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)
			allAdds = append(allAdds, adds...)
			for _, delHash := range delHashes {
				allDels[delHash] = struct{}{}
			}

			proof, err := m.Prove(delHashes)
			if err != nil {
				t.Fatal(err)
			}

			err = m.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatal(err)
			}
		}

		deleted := make([]bool, len(allAdds))
		for i := range deleted {
			_, found := allDels[allAdds[i].Hash]
			if found {
				deleted[i] = true
			}
		}

		memFile := newMemFile()
		tmpDir := t.TempDir()
		forest, err := newForest(memFile, newMemFile(), newMemFile(), nil, tmpDir+"/ctrl", tmpDir+"/slots", 17, 0)
		if err != nil {
			t.Fatal(err)
		}

		for i, add := range allAdds {
			if deleted[i] {
				err := forest.Modify([]Leaf{{Hash: empty}}, nil, Proof{})
				if err != nil {
					t.Fatal(err)
				}
			} else {
				err := forest.Modify([]Leaf{add}, nil, Proof{})
				if err != nil {
					t.Fatal(err)
				}
			}
		}

		roots := m.GetRoots()
		roots1 := forest.GetRoots()

		require.Equal(t, roots, roots1)
	})
}

// TestForestCachedRWSNoFlush verifies that when Forest is backed by cachedRWS,
// no data is written to the underlying files until Flush is called.
func TestForestNoFlushBeforeWAL(t *testing.T) {
	// Create the raw underlying memFiles.
	journal := newMemFile()
	underlyingFile := newMemFile()
	underlyingDelFile := newMemFile()
	underlyingBlockCountsFile := newMemFile()
	underlyingMetaFile := newMemFile()

	// WAL wraps files in cachedRWS (except bitmap) so writes are buffered.
	w, err := newWAL(journal, underlyingDelFile,
		walFile{File: underlyingFile, EntrySize: 32},
		walFile{File: underlyingBlockCountsFile, EntrySize: 4},
		walFile{File: underlyingMetaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	// Create forest backed by the WAL.
	tmpDir := t.TempDir()
	forest, err := newForest(w.Cached(0), w.Cached(1), w.Cached(2), w.Bitmap(), tmpDir+"/ctrl", tmpDir+"/slots", 10, 0)
	require.NoError(t, err)

	// Reference pollard for correctness comparison.
	pollard := NewAccumulator()

	// Add 8 leaves.
	leaves := make([]Leaf, 8)
	for i := range leaves {
		leaves[i] = Leaf{Hash: testHashFromInt(i + 1)}
	}
	err = forest.Modify(leaves, nil, Proof{})
	require.NoError(t, err)
	err = pollard.Modify(leaves, nil, Proof{})
	require.NoError(t, err)
	compareRoots(t, forest, pollard, "after adds")

	// Delete 2 leaves to exercise the deletion path.
	delHashes := []Hash{leaves[0].Hash, leaves[3].Hash}
	forestProof, err := forest.Prove(delHashes)
	require.NoError(t, err)
	err = forest.Modify(nil, delHashes, forestProof)
	require.NoError(t, err)

	pollardProof, err := pollard.Prove(delHashes)
	require.NoError(t, err)
	err = pollard.Modify(nil, delHashes, pollardProof)
	require.NoError(t, err)
	compareRoots(t, forest, pollard, "after deletes")

	// ---- KEY CHECK: underlying files must still be empty ----
	require.Equal(t, 0, len(underlyingFile.data),
		"main file should be untouched before Flush")
	require.Equal(t, 0, len(underlyingDelFile.data),
		"bitmap file should be untouched before Flush")
	require.Equal(t, 0, len(underlyingBlockCountsFile.data),
		"block counts file should be untouched before Flush")

	// Flush through WAL.
	require.NoError(t, w.Flush([32]byte{}))

	// Underlying files should now contain data.
	require.NotEqual(t, 0, len(underlyingFile.data),
		"main file should have data after Flush")
	require.NotEqual(t, 0, len(underlyingDelFile.data),
		"bitmap file should have data after Flush")
	require.NotEqual(t, 0, len(underlyingBlockCountsFile.data),
		"block counts file should have data after Flush")

	// Restart a new forest from the flushed underlying files.
	tmpDir2 := t.TempDir()
	bitmap2, err := loadDeletedBitmap(underlyingDelFile)
	require.NoError(t, err)
	forest2, err := newForest(
		underlyingFile, underlyingBlockCountsFile, underlyingMetaFile, bitmap2,
		tmpDir2+"/ctrl", tmpDir2+"/slots", 10, 0,
	)
	require.NoError(t, err)
	require.Equal(t, forest.GetRoots(), forest2.GetRoots(),
		"roots should match after restart from flushed data")
}

// TestForestCrashRecovery runs 400 blocks through simChain, flushes
// successfully at block 200, then continues through block 400 without
// flushing. A crash with a fully committed journal (valid checksum)
// is simulated. On recovery the WAL replays the journal and the forest
// should be at the block-400 state.
func TestForestCrashRecovery(t *testing.T) {
	journal := newMemFile()
	mainFile := newMemFile()
	delFile := newMemFile()
	blockCountsFile := newMemFile()
	metaFile := newMemFile()

	w, err := newWAL(journal, delFile,
		walFile{File: mainFile, EntrySize: 32},
		walFile{File: blockCountsFile, EntrySize: 4},
		walFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	tmpDir := t.TempDir()
	forest, err := newForest(w.Cached(0), w.Cached(1), w.Cached(2), w.Bitmap(), tmpDir+"/ctrl", tmpDir+"/slots", 16, 0)
	require.NoError(t, err)

	pollard := NewAccumulator()
	sc := newSimChainWithSeed(0x07, 0x07)

	var block200Roots []Hash

	for b := 1; b <= 400; b++ {
		adds, _, delHashes := sc.NextBlock(5)

		proof, err := pollard.Prove(delHashes)
		require.NoError(t, err)

		err = forest.Modify(adds, delHashes, proof)
		require.NoError(t, err)

		err = pollard.Modify(adds, delHashes, proof)
		require.NoError(t, err)

		compareRoots(t, forest, pollard, fmt.Sprintf("block %d", b))

		if b == 200 {
			require.NoError(t, w.Flush([32]byte{}))
			block200Roots = forest.GetRoots()
		}
	}

	block400Roots := forest.GetRoots()

	// ---- Simulate crash: journal committed but not applied ----
	require.NoError(t, w.crashAfterCommit())

	// Underlying files still only have block-200 data.
	tmpDir2 := t.TempDir()
	preRecoveryBitmap, err := loadDeletedBitmap(delFile)
	require.NoError(t, err)
	preRecoveryForest, err := newForest(
		mainFile, blockCountsFile, metaFile, preRecoveryBitmap,
		tmpDir2+"/ctrl", tmpDir2+"/slots", 16, 0,
	)
	require.NoError(t, err)
	require.Equal(t, block200Roots, preRecoveryForest.GetRoots(),
		"underlying files should still reflect block 200")

	// ---- "Restart": new WAL recovers from journal ----
	w2, err := newWAL(journal, delFile,
		walFile{File: mainFile, EntrySize: 32},
		walFile{File: blockCountsFile, EntrySize: 4},
		walFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	tmpDir3 := t.TempDir()
	recoveredForest, err := newForest(
		w2.Cached(0), w2.Cached(1), w2.Cached(2), w2.Bitmap(),
		tmpDir3+"/ctrl", tmpDir3+"/slots", 16, 0,
	)
	require.NoError(t, err)
	require.Equal(t, block400Roots, recoveredForest.GetRoots(),
		"recovered forest should reflect block 400 state")

	// Journal should be cleared after recovery.
	journal.Seek(0, io.SeekStart)
	var recoveredLen uint64
	err = binary.Read(journal, binary.LittleEndian, &recoveredLen)
	require.NoError(t, err)
	require.Equal(t, uint64(0), recoveredLen, "journal should be cleared")
}

// TestForestCrashIncompleteJournal runs 400 blocks through simChain,
// flushes successfully at block 200, then continues through block 400
// without flushing. A crash with an incomplete journal (no checksum)
// is simulated. On recovery the forest should be back at block 200.
func TestForestCrashIncompleteJournal(t *testing.T) {
	journal := newMemFile()
	mainFile := newMemFile()
	delFile := newMemFile()
	blockCountsFile := newMemFile()
	metaFile := newMemFile()

	w, err := newWAL(journal, delFile,
		walFile{File: mainFile, EntrySize: 32},
		walFile{File: blockCountsFile, EntrySize: 4},
		walFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	tmpDir := t.TempDir()
	forest, err := newForest(w.Cached(0), w.Cached(1), w.Cached(2), w.Bitmap(), tmpDir+"/ctrl", tmpDir+"/slots", 16, 0)
	require.NoError(t, err)

	pollard := NewAccumulator()
	sc := newSimChainWithSeed(0x07, 0x07)

	var savedRoots []Hash

	for b := 1; b <= 400; b++ {
		adds, _, delHashes := sc.NextBlock(5)

		proof, err := pollard.Prove(delHashes)
		require.NoError(t, err)

		err = forest.Modify(adds, delHashes, proof)
		require.NoError(t, err)

		err = pollard.Modify(adds, delHashes, proof)
		require.NoError(t, err)

		compareRoots(t, forest, pollard, fmt.Sprintf("block %d", b))

		if b == 200 {
			// Flush at block 200.
			require.NoError(t, w.Flush([32]byte{}))
			savedRoots = forest.GetRoots()
		}
	}

	// Blocks 200-399 are only in the cache. Simulate crash with
	// an incomplete journal write (no checksum).
	require.NoError(t, w.crashBeforeCommit())

	// "Restart": new WAL should discard the incomplete journal.
	w2, err := newWAL(journal, delFile,
		walFile{File: mainFile, EntrySize: 32},
		walFile{File: blockCountsFile, EntrySize: 4},
		walFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	// Forest should be back at the block-200 state.
	tmpDir2 := t.TempDir()
	recoveredForest, err := newForest(
		w2.Cached(0), w2.Cached(1), w2.Cached(2), w2.Bitmap(),
		tmpDir2+"/ctrl", tmpDir2+"/slots", 16, 0,
	)
	require.NoError(t, err)
	require.Equal(t, savedRoots, recoveredForest.GetRoots(),
		"forest should be at block 200 state after incomplete journal")
}

// TestForestVerifyDeletedLeaf tests that Verify correctly rejects leaves
// that have already been deleted. This specifically tests leaves with
// addIndex > 0 to catch bugs where packed values are used instead of
// unpacked positions.
func TestForestVerifyDeletedLeaf(t *testing.T) {
	forest := newTestForest(t, 8)

	// Add 4 leaves in one batch - they'll have addIndex 0, 1, 2, 3
	hashes := make([]Hash, 4)
	leaves := make([]Leaf, 4)
	for i := range 4 {
		hashes[i] = testHashFromInt(i)
		leaves[i] = Leaf{Hash: hashes[i]}
	}

	err := forest.Modify(leaves, nil, Proof{})
	require.NoError(t, err)

	// Verify all leaves exist
	for _, h := range hashes {
		err = forest.Verify([]Hash{h}, Proof{}, false)
		require.NoError(t, err, "leaf should exist before deletion")
	}

	// Delete leaf at index 2 (addIndex=2, which would cause bug if packed value used)
	delHash := hashes[2]
	err = forest.Modify(nil, []Hash{delHash}, Proof{})
	require.NoError(t, err)

	// Verify the deleted leaf should now fail
	err = forest.Verify([]Hash{delHash}, Proof{}, false)
	require.Error(t, err, "Verify should reject deleted leaf")
	require.Contains(t, err.Error(), "already been deleted")

	// Other leaves should still verify
	for i, h := range hashes {
		if i == 2 {
			continue // skip deleted
		}
		err = forest.Verify([]Hash{h}, Proof{}, false)
		require.NoError(t, err, "non-deleted leaf should still verify")
	}
}

// TestForestRebuildPositionMap verifies that rebuildPositionMap produces
// the same positionMap entries as the original Modify calls. It builds a
// forest over multiple blocks with varying add counts (including an empty
// block), snapshots every leaf's packed (addIndex, position) value, then
// clears and rebuilds the positionMap and checks all entries match.
func TestForestRebuildPositionMap(t *testing.T) {
	forest := newTestForest(t, 20)
	sc := newSimChainWithSeed(0x12, 0x34)

	// Run 10,000 blocks with adds and deletes.
	for range 10_000 {
		adds, _, delHashes := sc.NextBlock(5)
		err := forest.Modify(adds, delHashes, Proof{})
		require.NoError(t, err)
	}

	// Snapshot every leaf's packed value before rebuild.
	type leafEntry struct {
		hash   Hash
		packed uint64
	}
	allLeaves := make([]leafEntry, 0, forest.NumLeaves)
	for pos := uint64(0); pos < forest.NumLeaves; pos++ {
		hash, err := forest.readHash(pos)
		require.NoError(t, err)
		packed, found, err := forest.positionMap.Get(hash)
		require.NoError(t, err)
		require.True(t, found, "leaf at pos %d not found before rebuild", pos)
		allLeaves = append(allLeaves, leafEntry{hash: hash, packed: packed})
	}

	// Clear positionMap and rebuild.
	for _, le := range allLeaves {
		_, err := forest.positionMap.Delete(le.hash)
		require.NoError(t, err)
	}
	require.Equal(t, uint64(0), forest.positionMap.Count(), "positionMap should be empty after clearing")

	err := forest.rebuildPositionMap()
	require.NoError(t, err)

	// Verify every leaf has the same packed value as before.
	require.Equal(t, uint64(len(allLeaves)), forest.positionMap.Count(),
		"positionMap count mismatch after rebuild")
	for _, le := range allLeaves {
		got, found, err := forest.positionMap.Get(le.hash)
		require.NoError(t, err)
		require.True(t, found, "leaf not found after rebuild")
		require.Equal(t, le.packed, got,
			"packed value mismatch for leaf pos=%d addIndex=%d",
			unpackPos(le.packed), unpackIndex(le.packed))
	}
}

// TestForestUndoAfterRebuild verifies that Undo works correctly after
// restarting a Forest with a fresh Swiss Table (forcing positionMap rebuild).
// This catches bugs where the rebuilt positionMap is missing state needed
// for Undo to succeed.
func TestForestUndoAfterRebuild(t *testing.T) {
	// Shared backing files (persist across restarts).
	journal := newMemFile()
	mainFile := newMemFile()
	delFile := newMemFile()
	blockCountsFile := newMemFile()
	metaFile := newMemFile()

	w, err := newWAL(journal, delFile,
		walFile{File: mainFile, EntrySize: 32},
		walFile{File: blockCountsFile, EntrySize: 4},
		walFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	tmpDir1 := t.TempDir()
	forest, err := newForest(
		w.Cached(0), w.Cached(1), w.Cached(2), w.Bitmap(),
		tmpDir1+"/ctrl", tmpDir1+"/slots", 10, 0,
	)
	require.NoError(t, err)

	// Use a pollard as the reference accumulator.
	pollard := NewAccumulator()
	sc := newSimChainWithSeed(0x42, 0x42)

	// Run 100 blocks to build up state.
	for b := range 100 {
		adds, _, delHashes := sc.NextBlock(5)

		proof, err := pollard.Prove(delHashes)
		require.NoError(t, err)

		err = forest.Modify(adds, delHashes, Proof{})
		require.NoError(t, err)

		err = pollard.Modify(adds, delHashes, proof)
		require.NoError(t, err)

		compareRoots(t, forest, pollard, fmt.Sprintf("setup block %d", b))
	}

	// Checkpoint: save roots before the block we will undo.
	checkpointRoots := forest.GetRoots()

	// Run one more block — we will undo this one after restart.
	adds, _, delHashes := sc.NextBlock(5)

	proof, err := pollard.Prove(delHashes)
	require.NoError(t, err)

	err = forest.Modify(adds, delHashes, Proof{})
	require.NoError(t, err)

	err = pollard.Modify(adds, delHashes, proof)
	require.NoError(t, err)

	postModifyRoots := forest.GetRoots()
	compareRoots(t, forest, pollard, "after extra block")

	// Save undo args: extract hashes from adds for Undo's prevAdds parameter.
	prevAdds := make([]Hash, len(adds))
	for i, leaf := range adds {
		prevAdds[i] = leaf.Hash
	}

	// Flush to persist all state to underlying files before restart.
	require.NoError(t, w.Flush([32]byte{}))

	// Restart: new WAL + new tmpDir forces Swiss Table rebuild.
	w2, err := newWAL(journal, delFile,
		walFile{File: mainFile, EntrySize: 32},
		walFile{File: blockCountsFile, EntrySize: 4},
		walFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	tmpDir2 := t.TempDir()
	forest2, err := newForest(
		w2.Cached(0), w2.Cached(1), w2.Cached(2), w2.Bitmap(),
		tmpDir2+"/ctrl", tmpDir2+"/slots", 10, 0,
	)
	require.NoError(t, err)

	// Restarted forest should have the same roots as before restart.
	require.Equal(t, postModifyRoots, forest2.GetRoots(),
		"roots should match after restart with rebuilt positionMap")

	// Undo the last block on the restarted forest.
	err = forest2.Undo(prevAdds, Proof{}, delHashes, checkpointRoots)
	require.NoError(t, err)

	// After undo, roots should match the checkpoint.
	require.Equal(t, checkpointRoots, forest2.GetRoots(),
		"roots should match checkpoint after Undo on restarted forest")

	err = forest2.sanityCheck()
	require.NoError(t, err, "sanityCheck after Undo on restarted forest")
}

func TestOpenForest(t *testing.T) {
	tests := []struct {
		name        string
		adds        []Leaf
		delHashes   []Hash
		flushBefore bool // call Flush explicitly before Close
	}{
		{
			name: "add only",
			adds: []Leaf{
				{Hash: Hash{1}},
				{Hash: Hash{2}},
				{Hash: Hash{3}},
				{Hash: Hash{4}},
			},
		},
		{
			name: "add then delete",
			adds: []Leaf{
				{Hash: Hash{1}},
				{Hash: Hash{2}},
				{Hash: Hash{3}},
				{Hash: Hash{4}},
			},
			delHashes: []Hash{{2}},
		},
		{
			name: "flush then close",
			adds: []Leaf{
				{Hash: Hash{1}},
				{Hash: Hash{2}},
				{Hash: Hash{3}},
			},
			delHashes:   []Hash{{2}},
			flushBefore: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			dbpath := t.TempDir()

			forest, err := OpenForest(dbpath)
			require.NoError(t, err)

			err = forest.Modify(tt.adds, nil, Proof{})
			require.NoError(t, err)

			if len(tt.delHashes) > 0 {
				err = forest.Modify(nil, tt.delHashes, Proof{})
				require.NoError(t, err)
			}

			roots := forest.GetRoots()

			var bestHash [32]byte
			bestHash[0] = 0xAB
			if tt.flushBefore {
				require.NoError(t, forest.Flush(bestHash))
			}
			require.NoError(t, forest.Close(bestHash))

			// Reopen and verify state persisted.
			forest2, err := OpenForest(dbpath)
			require.NoError(t, err)
			defer forest2.Close(bestHash)

			require.Equal(t, roots, forest2.GetRoots(),
				"roots should match after reopen")
		})
	}
}

// TestForestBlockCountsReconciliation verifies that newForest trims stale
// block-count entries when the block counts file sum exceeds the
// WAL-protected numLeaves in metaFile. This can happen after an
// undo-without-flush crash.
func TestForestBlockCountsReconciliation(t *testing.T) {
	tests := []struct {
		name           string
		numLeaves      uint64
		blockCounts    []uint32 // initial block counts file contents
		expectedCounts []uint32 // block counts after reconciliation
	}{
		{
			name:           "one stale entry",
			numLeaves:      10,
			blockCounts:    []uint32{5, 5, 3},
			expectedCounts: []uint32{5, 5},
		},
		{
			name:           "two stale entries",
			numLeaves:      5,
			blockCounts:    []uint32{5, 5, 3},
			expectedCounts: []uint32{5},
		},
		{
			name:           "no stale entries",
			numLeaves:      13,
			blockCounts:    []uint32{5, 5, 3},
			expectedCounts: []uint32{5, 5, 3},
		},
		{
			name:           "fresh database",
			numLeaves:      0,
			blockCounts:    nil,
			expectedCounts: nil,
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			// -- metaFile: recordMode (32 zero bytes) + numLeaves as LE uint64 in a 32-byte entry --
			metaFile := newMemFile()
			var metaBuf [64]byte
			// bytes 0-31: recordMode (all zeros = not record mode)
			// bytes 32-39: numLeaves as LE uint64
			binary.LittleEndian.PutUint64(metaBuf[32:], tc.numLeaves)
			metaFile.Write(metaBuf[:])

			// -- blockCountsFile: uint32 LE entries --
			blockCountsFile := newMemFile()
			for _, c := range tc.blockCounts {
				binary.Write(blockCountsFile, binary.LittleEndian, c)
			}

			// -- mainFile: write 32-byte hashes for each leaf so rebuildPositionMap can read them --
			mainFile := newMemFile()
			for i := uint64(0); i < tc.numLeaves; i++ {
				h := testHashFromInt(int(i))
				mainFile.Write(h[:])
			}

			// Call newForest which triggers reconciliation and rebuildPositionMap.
			tmpDir := t.TempDir()
			forest, err := newForest(
				mainFile, blockCountsFile, metaFile, nil,
				tmpDir+"/ctrl", tmpDir+"/slots", 10, 0,
			)
			require.NoError(t, err)
			require.Equal(t, tc.numLeaves, forest.NumLeaves)

			// Read back block counts and verify they were trimmed.
			got, err := readBlockCounts(blockCountsFile)
			require.NoError(t, err)

			if tc.expectedCounts == nil {
				require.Empty(t, got, "expected no block counts")
			} else {
				require.Equal(t, tc.expectedCounts, got)
			}
		})
	}
}
