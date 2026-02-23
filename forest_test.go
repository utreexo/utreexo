package utreexo

import (
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"
	"reflect"
	"strings"
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
type memFile struct {
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
	if off >= int64(len(m.data)) {
		return 0, io.EOF
	}
	n := copy(p, m.data[off:])
	if n < len(p) {
		return n, io.EOF
	}
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

// TestForestString tests the ToString interface implementation.
func TestForestString(t *testing.T) {
	file := newMemFile()
	// Use small forestRows for visualization
	forest, err := NewForest(file, newMemFile(), newMemFile(), newMemFile(), 3)
	if err != nil {
		t.Fatalf("NewForest: %v", err)
	}

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
	file := newMemFile()
	forest, err := NewForest(file, newMemFile(), newMemFile(), newMemFile(), 10)
	if err != nil {
		t.Fatalf("NewForest: %v", err)
	}

	// Add 4 leaves
	hashes := make([]Hash, 4)
	for i := 0; i < 4; i++ {
		hashes[i] = testHashFromInt(i + 1)
		err := forest.add(hashes[i], 0)
		if err != nil {
			t.Fatalf("add %d: %v", i, err)
		}
	}

	// Valid forest should pass sanityCheck
	err = forest.sanityCheck()
	if err != nil {
		t.Fatalf("sanityCheck failed on valid forest: %v", err)
	}

	// Test 1: Corrupt positionMap by adding wrong entry
	// This should be caught by sanityCheck (either positionMap or parent verification)
	wrongHash := testHashFromInt(999)
	forest.positionMap[wrongHash.mini()] = packPosIndex(0, 0) // points to position 0, but hash there is hashes[0]
	err = forest.sanityCheck()
	if err == nil {
		t.Error("sanityCheck should fail with corrupted positionMap")
	}
	// Clean up
	delete(forest.positionMap, wrongHash.mini())

	// Test 2: Corrupt positionMap by pointing to wrong position
	// This should be caught by sanityCheck (either positionMap or parent verification)
	// Use position 1 instead of 99 since sanityCheck skips positions >= NumLeaves
	originalPacked := forest.positionMap[hashes[0].mini()]
	forest.positionMap[hashes[0].mini()] = packPosIndex(1, 0) // wrong position (has different hash)
	err = forest.sanityCheck()
	if err == nil {
		t.Error("sanityCheck should fail with wrong position in positionMap")
	}
	// Clean up
	forest.positionMap[hashes[0].mini()] = originalPacked

	// Test 3: Corrupt file by writing wrong hash to leaf position
	// This should be caught by sanityCheck (either positionMap or parent verification)
	err = forest.writeHash(0, wrongHash) // overwrite position 0 with wrong hash
	if err != nil {
		t.Fatal(err)
	}
	err = forest.sanityCheck()
	if err == nil {
		t.Error("sanityCheck should fail with corrupted file (leaf)")
	}
	// Restore
	err = forest.writeHash(0, hashes[0])
	if err != nil {
		t.Fatalf("failed to restore: %v", err)
	}

	// Test 4: Corrupt a root position directly and verify root check catches it
	// First verify sanityCheck passes after restoration
	err = forest.sanityCheck()
	if err != nil {
		t.Fatalf("sanityCheck should pass after restore: %v", err)
	}

	// Get root position and corrupt it
	// This should be caught by the path verification (invalid parent)
	rootPositions := RootPositions(forest.NumLeaves, forest.forestRows)
	if len(rootPositions) > 0 {
		rootPos := rootPositions[0]
		err = forest.writeHash(rootPos, wrongHash)
		if err != nil {
			t.Fatalf("failed to write to root: %v", err)
		}
		err = forest.sanityCheck()
		if err == nil {
			t.Error("sanityCheck should fail with corrupted root")
		} else if !strings.Contains(err.Error(), "invalid parent") {
			t.Errorf("expected invalid parent error, got: %v", err)
		}
	}
}

// sanityCheck checks for inconsistencies in the forest.
// This implements the UtreexoTest interface.
func (f *Forest) sanityCheck() error {
	// Check 0: Verify deletedLeafPositions map matches deletedFile length
	fileSize, err := f.deletedFile.Seek(0, io.SeekEnd)
	if err != nil {
		return fmt.Errorf("deletedFile seek: %w", err)
	}
	fileEntries := fileSize / 8
	mapEntries := int64(f.deletedLeafPositions.count())
	if fileEntries != mapEntries {
		return fmt.Errorf("deletedLeafPositions mismatch: file has %d entries, map has %d",
			fileEntries, mapEntries)
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

	for mini, packed := range f.positionMap {
		pos := unpackPos(packed)

		// Skip positions >= NumLeaves (undone additions)
		if pos >= f.NumLeaves {
			continue
		}
		// Skip deleted positions
		if f.deletedLeafPositions.isSet(pos) {
			continue
		}

		// Check 1: Verify positionMap entry matches file contents
		hash, err := cachedRead(pos)
		if err != nil {
			return fmt.Errorf("positionMap sanity: failed to read pos %d: %w", pos, err)
		}
		if hash.mini() != mini {
			return fmt.Errorf("positionMap sanity: pos %d has hash %x but map key is %x",
				pos, hash[:8], mini[:])
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
	for h, packed := range f.positionMap {
		pos := unpackPos(packed)

		// Skip positions >= NumLeaves (undone additions)
		if pos >= f.NumLeaves {
			continue
		}
		// Skip deleted positions
		if f.deletedLeafPositions.isSet(pos) {
			continue
		}
		if idx != 0 {
			sb.WriteString("\n")
		}
		fmt.Fprintf(&sb, "key:%s, pos:%d", hex.EncodeToString(h[:]), pos)
		idx++
	}
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
		delFile := newMemFile()
		forest, err := NewForest(memFile, delFile, newMemFile(), newMemFile(), 16)
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
		modifyForest, err := NewForest(newMemFile(), newMemFile(), newMemFile(), newMemFile(), 16)
		if err != nil {
			t.Fatal(err)
		}

		// Forest using Record + HashAll
		recordForest, err := NewForest(newMemFile(), newMemFile(), newMemFile(), newMemFile(), 16)
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
			_, err = recordForest.Record(addHashes, delHashes)
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
		delFile := newMemFile()
		forest, err := NewForest(memFile, delFile, newMemFile(), newMemFile(), 17)
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
func TestForestCachedRWSNoFlush(t *testing.T) {
	// Create the raw underlying memFiles.
	underlyingFile := newMemFile()
	underlyingDelFile := newMemFile()
	underlyingAddIdxFile := newMemFile()
	underlyingMetaFile := newMemFile()

	// Wrap each with cachedRWS so all writes are buffered.
	cachedFile, err := newCachedRWS(underlyingFile, 32, 0)
	require.NoError(t, err)
	cachedDelFile, err := newCachedRWS(underlyingDelFile, 8, 0)
	require.NoError(t, err)
	cachedAddIdxFile, err := newCachedRWS(underlyingAddIdxFile, 4, 0)
	require.NoError(t, err)
	cachedMetaFile, err := newCachedRWS(underlyingMetaFile, 32, 0)
	require.NoError(t, err)

	// Create forest backed by the cached files.
	forest, err := NewForest(cachedFile, cachedDelFile, cachedAddIdxFile, cachedMetaFile, 10)
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

	// Delete 2 leaves to exercise the deleted-file path as well.
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
		"deleted file should be untouched before Flush")
	require.Equal(t, 0, len(underlyingAddIdxFile.data),
		"addIndex file should be untouched before Flush")

	// Flush all caches to the underlying files.
	require.NoError(t, cachedFile.Flush())
	require.NoError(t, cachedDelFile.Flush())
	require.NoError(t, cachedAddIdxFile.Flush())

	// Underlying files should now contain data.
	require.NotEqual(t, 0, len(underlyingFile.data),
		"main file should have data after Flush")
	require.NotEqual(t, 0, len(underlyingDelFile.data),
		"deleted file should have data after Flush")
	require.NotEqual(t, 0, len(underlyingAddIdxFile.data),
		"addIndex file should have data after Flush")

	// Restart a new forest from the flushed underlying files
	// and verify the roots still match.
	forest2, err := NewForest(
		underlyingFile, underlyingDelFile, underlyingAddIdxFile, underlyingMetaFile, 10,
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
	addIdxFile := newMemFile()
	metaFile := newMemFile()

	w, err := NewWAL(journal,
		WALFile{File: mainFile, EntrySize: 32},
		WALFile{File: delFile, EntrySize: 8},
		WALFile{File: addIdxFile, EntrySize: 4},
		WALFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	forest, err := NewForest(w.Cached(0), w.Cached(1), w.Cached(2), w.Cached(3), 16)
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
	preRecoveryForest, err := NewForest(
		mainFile, delFile, addIdxFile, metaFile, 16,
	)
	require.NoError(t, err)
	require.Equal(t, block200Roots, preRecoveryForest.GetRoots(),
		"underlying files should still reflect block 200")

	// ---- "Restart": new WAL recovers from journal ----
	w2, err := NewWAL(journal,
		WALFile{File: mainFile, EntrySize: 32},
		WALFile{File: delFile, EntrySize: 8},
		WALFile{File: addIdxFile, EntrySize: 4},
		WALFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	recoveredForest, err := NewForest(
		w2.Cached(0), w2.Cached(1), w2.Cached(2), w2.Cached(3), 16,
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
	addIdxFile := newMemFile()
	metaFile := newMemFile()

	w, err := NewWAL(journal,
		WALFile{File: mainFile, EntrySize: 32},
		WALFile{File: delFile, EntrySize: 8},
		WALFile{File: addIdxFile, EntrySize: 4},
		WALFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	forest, err := NewForest(w.Cached(0), w.Cached(1), w.Cached(2), w.Cached(3), 16)
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
	w2, err := NewWAL(journal,
		WALFile{File: mainFile, EntrySize: 32},
		WALFile{File: delFile, EntrySize: 8},
		WALFile{File: addIdxFile, EntrySize: 4},
		WALFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	// Forest should be back at the block-200 state.
	recoveredForest, err := NewForest(
		w2.Cached(0), w2.Cached(1), w2.Cached(2), w2.Cached(3), 16,
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
	forest, err := NewForest(newMemFile(), newMemFile(), newMemFile(), newMemFile(), 8)
	require.NoError(t, err)

	// Add 4 leaves in one batch - they'll have addIndex 0, 1, 2, 3
	hashes := make([]Hash, 4)
	leaves := make([]Leaf, 4)
	for i := range 4 {
		hashes[i] = testHashFromInt(i)
		leaves[i] = Leaf{Hash: hashes[i]}
	}

	err = forest.Modify(leaves, nil, Proof{})
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
