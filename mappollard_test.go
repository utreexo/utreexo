package utreexo

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"math/rand"
	"reflect"
	"testing"

	"github.com/stretchr/testify/require"
	"golang.org/x/exp/slices"
)

// Assert that MapPollard implements the UtreexoTest interface.
var _ UtreexoTest = (*MapPollard)(nil)

// nodeMapToString returns the entire nodes of the mappollard as a human-readable string.
func (m *MapPollard) nodeMapToString() string {
	str := ""
	m.Nodes.ForEach(func(h Hash, n Node) error {
		keyStr := fmt.Sprintf("key:%s, node:%s",
			hex.EncodeToString(h[:]), n.String())
		str += "\n" + keyStr
		return nil
	})

	return str
}

// rootToString returns the roots as a string.
func (m *MapPollard) rootToString() string {
	return printHashes(m.GetRoots())
}

// sanityCheck checks that:
// 1: Unneeded nodes aren't cached.
// 2: Needed nodes for the cached leaves are cached.
// 3: Cached proof hashes up to the roots.
func (m *MapPollard) sanityCheck() error {
	err := m.checkProofNodes()
	if err != nil {
		return err
	}

	err = m.checkHashes()
	if err != nil {
		return err
	}

	return m.checkPointers()
}

// checkNodePointer recursively checks that the belows are also pointing to the parent and checks to make sure
// prunable nodes do not exist.
func (m *MapPollard) checkNodePointer(node Node, hash Hash) error {
	if (node.LBelow != empty) != (node.RBelow != empty) {
		return fmt.Errorf("belows should both be not empty or empty but for %v, "+
			"have l %v, r %v",
			hash, node.LBelow, node.RBelow)
	}
	if node.LBelow == empty {
		return nil
	}

	lNode, found := m.Nodes.Get(node.LBelow)
	if !found {
		return fmt.Errorf("node for %v has lbelow of %v but not found",
			hash, node.LBelow)
	}
	if lNode.Above != hash {
		return fmt.Errorf("node %v points to lbelow of %v but lbelow has above of %v",
			hash, node.LBelow, lNode.Above)
	}

	rNode, found := m.Nodes.Get(node.RBelow)
	if !found {
		return fmt.Errorf("node for %v has rbelow of %v but not found",
			hash, node.RBelow)
	}
	if rNode.Above != hash {
		return fmt.Errorf("node %v points to rbelow of %v but rbelow has above of %v",
			hash, node.RBelow, rNode.Above)
	}

	isPruneable, err := lNode.pruneable(rNode)
	if err != nil {
		return err
	}
	if isPruneable {
		return fmt.Errorf("nodes:\nl (%v) %v\nr (%v) %v\nis pruneable but is present",
			node.LBelow, lNode.String(), node.RBelow, rNode.String())
	}

	err = m.checkNodePointer(lNode, node.LBelow)
	if err != nil {
		return err
	}

	err = m.checkNodePointer(rNode, node.RBelow)
	if err != nil {
		return err
	}

	return nil
}

// checkPointers checks that all the belows of the nodes are also pointing up and
// also checks that all prunable nodes are not cached.
func (m *MapPollard) checkPointers() error {
	for _, root := range m.Roots {
		if root == empty {
			continue
		}
		node, found := m.Nodes.Get(root)
		if !found {
			return fmt.Errorf("root hash of %v not found", root)
		}

		err := m.checkNodePointer(node, root)
		if err != nil {
			return err
		}
	}

	return nil
}

// checkProofNodes checks that all the proof positions needed to cache a proof exists in the map
// of nodes.
func (m *MapPollard) checkProofNodes() error {
	// Sanity check.
	return m.Nodes.ForEach(func(k Hash, v Node) error {
		if m.Full && v.AddIndex == -1 {
			return nil
		}
		if !v.Remember {
			return nil
		}

		position, err := m.calculatePosition(k, v)
		if err != nil {
			return err
		}
		proofPos := proofPosition(position, m.NumLeaves, m.TotalRows)

		hashes, err := m.getHashesByPositions(proofPos)
		if err != nil {
			return fmt.Errorf("Corrupted pollard. errored while "+
				"fetching hashes for proving %d. %v", position, err)
		}

		for i, hash := range hashes {
			pos := proofPos[i]
			if hash == empty {
				return fmt.Errorf("Corrupted pollard. Missing pos %d "+
					"needed for proving %d", pos, position)
			}
		}

		return nil
	})
}

// checkHashes checks that the leaves correctly hash up to the roots. Returns an error if
// any of the roots or the intermediate nodes don't match up with the calculated hashes.
func (m *MapPollard) checkHashes() error {
	if m.Nodes.Length() == 0 {
		return nil
	}

	leafHashes := make([]Hash, 0, m.Nodes.Length())
	m.Nodes.ForEach(func(hash Hash, node Node) error {
		if m.Full && node.AddIndex == -1 {
			return nil
		}
		if !node.Remember {
			return nil
		}

		leafHashes = append(leafHashes, hash)
		return nil
	})

	proof, err := m.Prove(leafHashes)
	if err != nil {
		return err
	}

	haveRoots := m.getRoots()
	rootIndexes, err := Verify(Stump{Roots: haveRoots, NumLeaves: m.NumLeaves}, leafHashes, proof)
	if err != nil {
		return fmt.Errorf("Failed to verify proof:\n%s\ndelHashes:\n%s\nerr: %v\n", proof.String(), printHashes(leafHashes), err)
	}

	// Check roots.
	intermediate, gotRoots, err := calculateHashes(m.NumLeaves, leafHashes, proof)
	if err != nil {
		return err
	}
	if len(gotRoots) != len(rootIndexes) {
		return fmt.Errorf("expected %d calculated roots but got %d", len(gotRoots), len(rootIndexes))
	}

	for i, rootIdx := range rootIndexes {
		if haveRoots[rootIdx] != gotRoots[i] {
			return fmt.Errorf("calculated %s but have %s",
				hex.EncodeToString(gotRoots[i][:]),
				hex.EncodeToString(haveRoots[rootIdx][:]))
		}
	}

	// Check all intermediate nodes.
	for i, pos := range intermediate.positions {
		hash := m.GetHash(pos)
		if hash == empty {
			continue
		}
		gotHash := intermediate.hashes[i]

		if hash != gotHash {
			return fmt.Errorf("For position %d, calculated %s but have %s",
				pos, hex.EncodeToString(gotHash[:]), hex.EncodeToString(hash[:]))
		}
	}

	return nil
}

// checkEqualProof checks that the two proofs are the same.
func (p *Proof) checkEqualProof(other Proof) error {
	if len(other.Targets) != len(p.Targets) {
		return fmt.Errorf("Have %d targets but other has %d targets. mine: %v, other: %v",
			len(p.Targets), len(other.Targets), p.Targets, other.Targets)
	}

	for i := range p.Targets {
		if p.Targets[i] != other.Targets[i] {
			return fmt.Errorf("At idx %d have %d but other has %d. sorted mine: %v, sorted other: %v",
				i, p.Targets[i], other.Targets[i], p.Targets, other.Targets)
		}
	}

	if len(other.Proof) != len(p.Proof) {
		return fmt.Errorf("Have %d proof but other has %d proof.\nMine:\n%s\nother:\n%s\n",
			len(p.Proof), len(other.Proof), printHashes(p.Proof), printHashes(other.Proof))
	}

	for i := range p.Proof {
		if p.Proof[i] != other.Proof[i] {
			return fmt.Errorf("At idx %d have %s but other has %s.\nMine:\n%s\nother:\n%s\n",
				i, p.Proof[i], other.Proof[i], printHashes(p.Proof), printHashes(other.Proof))
		}
	}

	return nil
}

func TestMapPollardView(t *testing.T) {
	// newPollard returns the same fully cached accumulator for each independent
	// test state.
	newPollard := func(t *testing.T) *MapPollard {
		t.Helper()

		// Build eight remembered leaves so the pollard contains the complete
		// tree needed by both cache cases.
		leaves := make([]Leaf, 8)
		for i := range leaves {
			leaves[i] = Leaf{
				Hash:     sha256.Sum256([]byte{uint8(i)}),
				Remember: true,
			}
		}

		pollard := NewMapPollard(false)
		err := pollard.Modify(leaves, nil, Proof{})
		require.NoError(t, err)
		return &pollard
	}

	// Exercise preparation with nodes already cached and with nodes supplied by
	// proof ingestion.
	tests := []struct {
		name      string
		rootsOnly bool
	}{
		{
			name: "fully cached pollard",
		},
		{
			name:      "roots only pollard",
			rootsOnly: true,
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			// Generate the deletion proof from a complete accumulator.
			full := newPollard(t)
			delHash := sha256.Sum256([]byte{2})
			delHashes := []Hash{delHash}
			proof, err := full.Prove(delHashes)
			require.NoError(t, err)
			adds := []Leaf{{
				Hash:     sha256.Sum256([]byte{8}),
				Remember: true,
			}}

			// Initialize matching pollards with the cache state selected by the
			// test case.
			pollard := newPollard(t)
			expected := newPollard(t)
			if test.rootsOnly {
				pollard = InitWithStump(full.GetStump())
				pollard.TotalRows = full.TotalRows
				expected = InitWithStump(full.GetStump())
				expected.TotalRows = full.TotalRows
			}

			// Snapshot every part of the live pollard before preparing the view.
			beforeStump := pollard.GetStump()
			beforeRows := pollard.GetTreeRows()
			beforeNodes := copyMapPollardNodes(t, pollard)

			// Prepare the modification and keep it private to the returned view.
			view, err := pollard.PrepareModify(adds, delHashes, proof)
			require.NoError(t, err)

			// Preparation must leave the live accumulator and its cache unchanged.
			require.Equal(t, beforeStump, pollard.GetStump())
			require.Equal(t, beforeRows, pollard.GetTreeRows())
			require.Equal(t, beforeNodes, copyMapPollardNodes(t, pollard))

			// Apply the same proof and modification through the established direct
			// flow to obtain the expected state.
			err = expected.Verify(delHashes, proof, true)
			require.NoError(t, err)
			err = expected.Modify(adds, delHashes, proof)
			require.NoError(t, err)

			// The prepared view must expose the state produced by the direct flow.
			require.Equal(t, expected.GetStump(), view.GetStump())
			require.Equal(t, expected.GetTreeRows(), view.GetTreeRows())

			// Committing must publish the complete expected state exactly once.
			require.NoError(t, view.Commit())
			require.Equal(t, expected.GetStump(), pollard.GetStump())
			require.Equal(t, expected.GetTreeRows(), pollard.GetTreeRows())
			require.Equal(t, copyMapPollardNodes(t, expected),
				copyMapPollardNodes(t, pollard))
			require.NoError(t, pollard.sanityCheck())
			require.ErrorContains(t, view.Commit(), "already committed")
		})
	}
}

// copyMapPollardNodes returns a copy of every node cached by the map pollard.
func copyMapPollardNodes(t *testing.T, m *MapPollard) map[Hash]Node {
	t.Helper()

	// Copy through NodesInterface so the comparison also works with alternate
	// node storage implementations.
	nodes := make(map[Hash]Node, m.Nodes.Length())
	err := m.Nodes.ForEach(func(hash Hash, node Node) error {
		nodes[hash] = node
		return nil
	})
	require.NoError(t, err)

	return nodes
}

func TestMapPollardUndoView(t *testing.T) {
	// Build a pollard with a full tree so both the fully cached and the roots
	// only cache cases can be exercised.
	newPollard := func(t *testing.T) *MapPollard {
		t.Helper()

		leaves := make([]Leaf, 8)
		for i := range leaves {
			leaves[i] = Leaf{
				Hash:     sha256.Sum256([]byte{uint8(i)}),
				Remember: true,
			}
		}

		pollard := NewMapPollard(false)
		err := pollard.Modify(leaves, nil, Proof{})
		require.NoError(t, err)
		return &pollard
	}

	tests := []struct {
		name      string
		rootsOnly bool
	}{
		{
			name: "fully cached pollard",
		},
		{
			name:      "roots only pollard",
			rootsOnly: true,
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			// Generate the modify to undo from a complete accumulator.
			full := newPollard(t)
			delHash := sha256.Sum256([]byte{2})
			delHashes := []Hash{delHash}
			proof, err := full.Prove(delHashes)
			require.NoError(t, err)
			adds := []Leaf{{
				Hash:     sha256.Sum256([]byte{8}),
				Remember: true,
			}}
			addHashes := []Hash{adds[0].Hash}

			// Initialize matching pollards with the cache state selected by the
			// test case.
			pollard := newPollard(t)
			expected := newPollard(t)
			if test.rootsOnly {
				pollard = InitWithStump(full.GetStump())
				pollard.TotalRows = full.TotalRows
				expected = InitWithStump(full.GetStump())
				expected.TotalRows = full.TotalRows
			}

			// Apply the modify to both pollards and remember the state before it.
			origRoots := pollard.GetRoots()
			err = pollard.Modify(adds, delHashes, proof)
			require.NoError(t, err)
			err = expected.Modify(adds, delHashes, proof)
			require.NoError(t, err)

			// Snapshot every part of the live pollard before preparing the view.
			beforeStump := pollard.GetStump()
			beforeRows := pollard.GetTreeRows()
			beforeNodes := copyMapPollardNodes(t, pollard)

			// Prepare the undo and keep it private to the returned view.
			view, err := pollard.PrepareUndo(addHashes, nil, proof, delHashes, origRoots)
			require.NoError(t, err)

			// Preparation must leave the live accumulator and its cache unchanged.
			require.Equal(t, beforeStump, pollard.GetStump())
			require.Equal(t, beforeRows, pollard.GetTreeRows())
			require.Equal(t, beforeNodes, copyMapPollardNodes(t, pollard))

			// Undo the modify through the established direct flow to obtain the
			// expected state.
			err = expected.Undo(addHashes, proof, delHashes, origRoots)
			require.NoError(t, err)

			// The prepared view must expose the state produced by the direct flow.
			require.Equal(t, expected.GetStump(), view.GetStump())
			require.Equal(t, expected.GetTreeRows(), view.GetTreeRows())

			// Committing must publish the complete expected state exactly once.
			require.NoError(t, view.Commit())
			require.Equal(t, expected.GetStump(), pollard.GetStump())
			require.Equal(t, expected.GetTreeRows(), pollard.GetTreeRows())
			require.Equal(t, copyMapPollardNodes(t, expected),
				copyMapPollardNodes(t, pollard))
			require.NoError(t, pollard.sanityCheck())
			require.ErrorContains(t, view.Commit(), "already committed")
		})
	}
}

func FuzzMapPollardChain(f *testing.F) {
	// Seed the fuzz target with a chain that performs repeated additions and
	// deletions.
	tests := []struct {
		numAdds  uint32
		duration uint32
		seed     int64
	}{
		{3, 0x07, 0x07},
	}

	// Register each table entry as a deterministic fuzz seed.
	for _, test := range tests {
		f.Add(test.numAdds, test.duration, test.seed)
	}

	f.Fuzz(func(t *testing.T, numAdds, duration uint32, seed int64) {
		t.Parallel()

		// Generate a deterministic sequence of accumulator modifications.
		sc := newSimChainWithSeed(duration, seed)

		// Maintain the direct map pollard, the staged map pollard, and the full
		// accumulator across the same chain.
		m := NewMapPollard(false)
		staged := NewMapPollard(false)
		full := NewAccumulator()

		var totalAdds, totalDels int
		for b := 0; b <= 50; b++ {
			// Generate the additions and deletions for the next simulated block.
			adds, _, delHashes := sc.NextBlock(numAdds)
			totalAdds += len(adds)
			totalDels += len(delHashes)

			// Produce the proof from the full accumulator, which retains every
			// node required to prove the deletions.
			expectProof, err := full.Prove(delHashes)
			if err != nil {
				t.Fatal(err)
			}

			// Ingest and verify the proof through the direct map pollard flow.
			err = m.Verify(delHashes, expectProof, true)
			if err != nil {
				t.Fatalf("%v\nproving delHashes:\nproof:\n%s\n%s\nmap:\n%s\nfull:\n%s\n",
					err, printHashes(delHashes), expectProof.String(),
					m.String(), full.String())
			}

			// Prove the same deletions from the nodes now cached by the map
			// pollard.
			proof, err := m.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzMapPollardChain fail at block %d. Couldn't prove\n%s\nError: %v",
					b, printHashes(delHashes), err)
			}

			// Require the map pollard proof to match the full accumulator proof.
			err = proof.checkEqualProof(expectProof)
			if err != nil {
				t.Fatalf("\nFor delhashes: %v\nexpected proof:\n%s\ngot:\n%s\nerr: %v\n"+
					"maptreexo:\n%s\nfull:\n%s\n",
					printHashes(delHashes), expectProof.String(), proof.String(), err,
					m.String(), full.String())
			}

			// Confirm that every proof target is present in the map pollard.
			for _, target := range proof.Targets {
				fetch := target
				if defaultForestRows != m.TotalRows {
					fetch = translatePos(fetch, defaultForestRows, m.TotalRows)
				}
				hash := m.GetHash(fetch)
				if hash == empty {
					t.Fatalf("FuzzMapPollardChain doesn't have the hash "+
						"for %d at block %d.", target, b)
				}
			}

			// Snapshot every part of the staged pollard before preparation.
			stumpBefore := staged.GetStump()
			rowsBefore := staged.GetTreeRows()
			nodesBefore := copyMapPollardNodes(t, &staged)

			// Prepare the block modification in a private view.
			view, err := staged.PrepareModify(adds, delHashes, expectProof)
			if err != nil {
				t.Fatalf("FuzzMapPollardChain fail while preparing block %d. Error: %v",
					b, err)
			}

			// Preparation must leave the live stump, tree rows, and cache
			// unchanged.
			if !reflect.DeepEqual(stumpBefore, staged.GetStump()) {
				t.Fatalf("FuzzMapPollardChain changed accumulator state while preparing block %d", b)
			}
			if rowsBefore != staged.GetTreeRows() {
				t.Fatalf("FuzzMapPollardChain changed tree rows while preparing block %d", b)
			}
			if !reflect.DeepEqual(nodesBefore, copyMapPollardNodes(t, &staged)) {
				t.Fatalf("FuzzMapPollardChain changed cached nodes while preparing block %d", b)
			}

			// Apply the block through the direct and full accumulator flows, then
			// publish the prepared view.
			err = m.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("FuzzMapPollardChain fail at block %d. Error: %v", b, err)
			}

			err = full.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatal(err)
			}
			err = view.Commit()
			if err != nil {
				t.Fatalf("FuzzMapPollardChain fail while committing block %d. Error: %v",
					b, err)
			}

			// Committing the prepared modification must produce the same
			// accumulator and cache as ingesting and modifying directly.
			if !reflect.DeepEqual(copyMapPollardNodes(t, &m),
				copyMapPollardNodes(t, &staged)) {
				t.Fatalf("FuzzMapPollardChain cached nodes differ at block %d", b)
			}
			if !reflect.DeepEqual(m.GetStump(), staged.GetStump()) {
				t.Fatalf("FuzzMapPollardChain accumulator state differs at block %d", b)
			}
			if m.GetTreeRows() != staged.GetTreeRows() {
				t.Fatalf("FuzzMapPollardChain tree rows differ at block %d", b)
			}

			// Collect every remembered leaf cached by the direct map pollard.
			cachedHashes := make([]Hash, 0, m.Nodes.Length())
			leafHashes := make([]Hash, 0, m.Nodes.Length())
			m.Nodes.ForEach(func(k Hash, v Node) error {
				if v.Remember {
					cachedHashes = append(cachedHashes, k)
					leafHashes = append(leafHashes, k)
				}
				return nil
			})

			if !reflect.DeepEqual(cachedHashes, leafHashes) {
				err := fmt.Errorf("Fail at block %d\ngot cachedHashes:\n%s\n"+
					"leafHashes:\n%s\nmaptreexo:\n%s\nfull:\n%s\n",
					b, printHashes(cachedHashes), printHashes(leafHashes),
					m.String(), full.String())
				t.Fatal(err)
			}

			// Compare proofs for the cached leaves against the full accumulator.
			cachedProofExpect, err := full.Prove(cachedHashes)
			if err != nil {
				t.Fatal(err)
			}

			cachedProof, err := m.Prove(leafHashes)
			if err != nil {
				t.Fatal(err)
			}

			err = cachedProof.checkEqualProof(cachedProofExpect)
			if err != nil {
				t.Fatalf("\nFor delhashes: %v\nexpected proof:\n%s\ngot:\n%s\nerr: %v\n"+
					"maptreexo:\n%s\nfull:\n%s\n",
					printHashes(cachedHashes), cachedProofExpect.String(), cachedProof.String(),
					err, m.String(), full.String())
			}

			// Exercise proof completion using the validated cached proof.
			testMakeProofFull(t, m, cachedProof)

			// Finish the block by comparing roots and checking map pollard
			// structure.
			fullRoots := full.GetRoots()
			mapRoots := m.GetRoots()
			if !reflect.DeepEqual(fullRoots, mapRoots) {
				t.Fatalf("Roots differ. expected:\n%s\nbut got:\n%s\nfull:\n%s\nmap:\n%s\n",
					printHashes(fullRoots), printHashes(mapRoots), full.String(), m.String())
			}

			err = m.sanityCheck()
			if err != nil {
				t.Fatal(err)
			}
		}
	})
}

func testMakeProofFull(t *testing.T, m MapPollard, proof Proof) {
	if len(proof.Proof) == 0 || len(proof.Targets) == 0 {
		return
	}

	haves := make([]bool, len(proof.Proof))
	proofHashes := make([]Hash, 0, len(proof.Proof))
	for i, proofHash := range proof.Proof {
		if rand.Int()%2 == 0 {
			haves[i] = true
			proofHashes = append(proofHashes, proofHash)
		}
	}

	gotProof, err := m.MakeProofFull(proof.Targets, haves, proofHashes)
	if err != nil {
		t.Fatal(err)
	}

	require.Equal(t, proof, *gotProof)

	for i := range haves {
		if !haves[i] {
			haves[i] = true
		} else {
			haves[i] = false
		}
	}

	wrongProof, err := m.MakeProofFull(proof.Targets, haves, proofHashes)
	if err == nil {
		// A wrong proof is not guaranteed to produce an error so we need to check
		// this.
		require.NotEqual(t, proof, *wrongProof)
	}
}

func FuzzMapPollardWriteAndRead(f *testing.F) {
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

		m := NewMapPollard(false)
		for b := 0; b <= 20; b++ {
			adds, durations, delHashes := sc.NextBlock(numAdds)
			for i, duration := range durations {
				if duration != 0 {
					adds[i].Remember = true
				}
			}

			proof, err := m.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzWriteAndRead fail at block %d. Error: %v", b, err)
			}

			err = m.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("FuzzWriteAndRead fail at block %d. Error: %v", b, err)
			}
		}
		err := m.checkHashes()
		if err != nil {
			t.Fatal(err)
		}

		var buf bytes.Buffer
		wroteBytes, err := m.Write(&buf)
		if err != nil {
			t.Fatal(err)
		}

		if wroteBytes != len(buf.Bytes()) {
			t.Fatalf("FuzzWriteAndRead Fail. Wrote %d but serializeSize got %d",
				wroteBytes, len(buf.Bytes()))
		}

		m1 := NewMapPollard(false)

		// Restore from the buffer.
		readBytes, err := m1.Read(&buf)
		if err != nil {
			t.Fatal(err)
		}
		if readBytes != wroteBytes {
			t.Fatalf("FuzzWriteAndRead Fail. Wrote %d but read %d", readBytes, wroteBytes)
		}

		// Check that the hashes of the roots are correct.
		err = m1.checkHashes()
		if err != nil {
			t.Fatal(err)
		}
	})
}

func FuzzMapPollardPrune(f *testing.F) {
	var tests = []struct {
		startLeaves uint32
		modifyAdds  uint32
		delCount    uint32
	}{
		{3, 4, 1},
	}
	for _, test := range tests {
		f.Add(test.startLeaves, test.modifyAdds, test.delCount)
	}

	f.Fuzz(func(t *testing.T, startLeaves uint32, modifyAdds uint32, delCount uint32) {
		t.Parallel()

		// delCount must be less than the current number of leaves.
		if delCount >= startLeaves {
			return
		}

		// Boilerplate for generating a pollard.
		leaves, delHashes, _ := getAddsAndDels(0, startLeaves, delCount)
		acc := NewMapPollard(false)
		err := acc.Modify(leaves, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}
		proof, err := acc.Prove(delHashes)
		if err != nil {
			t.Fatal(err)
		}
		modifyLeaves, _, _ := getAddsAndDels(uint32(acc.GetNumLeaves()), modifyAdds, 0)
		err = acc.Modify(modifyLeaves, delHashes, proof)
		if err != nil {
			t.Fatal(err)
		}

		// Collect cached leaves.
		cachedLeaves := make([]Hash, 0, acc.Nodes.Length())
		acc.Nodes.ForEach(func(k Hash, v Node) error {
			if v.Remember {
				cachedLeaves = append(cachedLeaves, k)
			}
			return nil
		})

		// Return now since we don't have anything to prune.
		if len(cachedLeaves) == 0 {
			return
		}

		// Randomly choose targets to prune.
		count := rand.Intn(len(cachedLeaves))
		prunedPositions := make([]uint64, 0, count)
		targets := make([]uint64, 0, len(cachedLeaves))

		toPrune := make([]Hash, 0, count)
		notPruned := make([]Hash, 0, len(cachedLeaves)-count)

		for _, leafHash := range cachedLeaves {
			node, _ := acc.Nodes.Get(leafHash)
			pos, err := acc.calculatePosition(leafHash, node)
			if err != nil {
				t.Fatal(err)
			}

			if len(toPrune) >= count {
				targets = append(targets, pos)
				notPruned = append(notPruned, leafHash)
			}
			if rand.Int()%2 == 0 {
				toPrune = append(toPrune, leafHash)
				prunedPositions = append(prunedPositions, pos)
			} else {
				targets = append(targets, pos)
				notPruned = append(notPruned, leafHash)
			}
		}
		slices.Sort(targets)
		slices.Sort(prunedPositions)

		// Calculate the nodes that should not exist after the prune.
		shouldNotExist, _ := ProofPositions(prunedPositions, acc.NumLeaves, acc.TotalRows)
		exist, _ := ProofPositions(targets, acc.NumLeaves, acc.TotalRows)
		shouldNotExist = subtractSortedSlice(shouldNotExist, exist, uint64Cmp)

		// Prune the randomly chosen hashes from the accumulator.
		err = acc.Prune(toPrune)
		if err != nil {
			t.Fatal(err)
		}

		// Check that the not pruned hashes are able to be proven.
		proof, err = acc.Prove(notPruned)
		if err != nil {
			t.Fatal(err)
		}
		err = acc.Verify(notPruned, proof, false)
		if err != nil {
			t.Fatal(err)
		}

		// Check that the positions that should not exist actually don't exist.
		for _, pos := range shouldNotExist {
			hash := acc.GetHash(pos)
			if hash != empty {
				t.Fatalf("position %d shouldn't exist", pos)
			}
		}
	})
}

// singleModify is a struct with adds and dels that makes it easier to create mock
// accumulators for testing purposes.
type singleModify struct {
	adds []Leaf
	dels []Hash
}

// applySingleModify applies a single modify to the passed in accumulator.
func applySingleModify(utreexo Utreexo, adds []Leaf, dels []Hash) error {
	// No leaves means that it's just been created. In that case, don't
	// add and delete in a single modify as that'll cause an error.
	if utreexo.GetNumLeaves() == 0 {
		err := utreexo.Modify(adds, nil, Proof{})
		if err != nil {
			return err
		}
		proof, err := utreexo.Prove(dels)
		if err != nil {
			return err
		}
		err = utreexo.Modify(nil, dels, proof)
		if err != nil {
			return err
		}

		return nil
	}
	proof, err := utreexo.Prove(dels)
	if err != nil {
		return err
	}
	err = utreexo.Modify(adds, dels, proof)
	if err != nil {
		return err
	}

	return nil
}

// proofViewTestCase contains a map pollard and a view with an ingested
// deletion proof.
type proofViewTestCase struct {
	name     string
	pollard  *MapPollard
	view     *view
	rootHash Hash
	rootNode Node
}

// buildProofViewTestCase creates the state shared by the view lookup tests.
func buildProofViewTestCase(t *testing.T, name string,
	delIndexes []int) proofViewTestCase {

	t.Helper()

	// Build a complete pollard that can generate the deletion proof.
	leaves := make([]Leaf, 8)
	for i := range leaves {
		leaves[i] = Leaf{
			Hash:     sha256.Sum256([]byte{uint8(i)}),
			Remember: true,
		}
	}
	full := NewMapPollard(false)
	require.NoError(t, full.Modify(leaves, nil, Proof{}))

	// Generate the proof and the same ingest instruction used by the map
	// pollard proof path.
	delHashes := make([]Hash, len(delIndexes))
	for i, index := range delIndexes {
		delHashes[i] = leaves[index].Hash
	}
	proof, err := full.Prove(delHashes)
	require.NoError(t, err)
	ingestIns, _, _, err := generateIngestAndUndoInfo(
		full.NumLeaves, delHashes, proof)
	require.NoError(t, err)

	// Initialize the map pollard with roots only, then copy those roots into
	// the view before ingesting the proof.
	pollard := InitWithStump(full.GetStump())
	pollard.TotalRows = full.TotalRows
	proofView := initView(pollard.Roots, len(delHashes))
	proofView.numLeaves = pollard.NumLeaves
	proofView.totalRows = pollard.TotalRows
	for _, root := range pollard.Roots {
		rootNode, found := pollard.Nodes.Get(root)
		require.True(t, found)
		proofView.nodes[root] = rootNode
	}
	require.NoError(t, proofView.ingest(ingestIns))

	// Select a root whose node has child hashes after proof ingestion.
	var rootHash Hash
	var rootNode Node
	for _, root := range pollard.Roots {
		node := proofView.nodes[root]
		if node.LBelow != empty {
			rootHash = root
			rootNode = node
			break
		}
	}
	require.NotEqual(t, Hash(empty), rootHash)

	return proofViewTestCase{
		name:     name,
		pollard:  pollard,
		view:     proofView,
		rootHash: rootHash,
		rootNode: rootNode,
	}
}

func TestViewFetchAndCacheNodeAfterProofIngestion(t *testing.T) {
	// Build the complete input state for each proof shape before running the
	// assertions.
	tests := []proofViewTestCase{
		buildProofViewTestCase(t, "single deletion", []int{2}),
		buildProofViewTestCase(t, "deletions in both branches", []int{1, 6}),
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			// The root hash is present in both caches. The map pollard node has
			// empty child hashes, while the view node has the child hashes
			// supplied by the proof.
			mapRoot, found := test.pollard.Nodes.Get(test.rootHash)
			require.True(t, found)
			require.Equal(t, Hash(empty), mapRoot.LBelow)
			require.Equal(t, Hash(empty), mapRoot.RBelow)
			require.NotEqual(t, Hash(empty), test.rootNode.LBelow)
			require.NotEqual(t, Hash(empty), test.rootNode.RBelow)

			// The lookup must return the node already present in the view.
			gotRoot, found := test.view.fetchAndCacheNode(test.pollard,
				test.rootHash)
			require.True(t, found)
			require.Equal(t, test.rootNode, gotRoot)
		})
	}
}

// cacheBelowsTestCase contains the expected children for a root whose child
// nodes are split between the map pollard and the view.
type cacheBelowsTestCase struct {
	proofViewTestCase
	leftChild  Node
	rightChild Node
}

// buildCacheBelowsTestCase places one child in each node cache.
func buildCacheBelowsTestCase(t *testing.T, name string,
	delIndexes []int) cacheBelowsTestCase {

	t.Helper()

	test := buildProofViewTestCase(t, name, delIndexes)
	leftChild, found := test.view.nodes[test.rootNode.LBelow]
	require.True(t, found)
	rightChild, found := test.view.nodes[test.rootNode.RBelow]
	require.True(t, found)

	// Keep the left child only in the map pollard and the right child only
	// in the view. cacheBelows must resolve both sources.
	delete(test.view.nodes, test.rootNode.LBelow)
	test.pollard.Nodes.Put(test.rootNode.LBelow, leftChild)

	return cacheBelowsTestCase{
		proofViewTestCase: test,
		leftChild:         leftChild,
		rightChild:        rightChild,
	}
}

func TestViewCacheBelowsAfterProofIngestion(t *testing.T) {
	// Build the complete input state for each proof shape before running the
	// assertions.
	tests := []cacheBelowsTestCase{
		buildCacheBelowsTestCase(t, "single deletion", []int{2}),
		buildCacheBelowsTestCase(t, "deletions in both branches", []int{1, 6}),
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			// cacheBelows must copy the left child from the map pollard and retain
			// the right child from the view.
			require.NoError(t, test.view.cacheBelows(test.pollard,
				test.rootNode))

			leftChild, found := test.view.nodes[test.rootNode.LBelow]
			require.True(t, found)
			require.Equal(t, test.leftChild, leftChild)
			rightChild, found := test.view.nodes[test.rootNode.RBelow]
			require.True(t, found)
			require.Equal(t, test.rightChild, rightChild)
		})
	}
}

func TestGetMissingPositions(t *testing.T) {
	tests := []struct {
		mods   []singleModify
		proves [][]uint64
	}{
		// Creates a tree like below.
		//
		// |-----------------------\
		// 28
		// |-----------\           |-----------\
		//             25
		// |-----\     |-----\     |-----\     |-----\
		// 16
		// |--\  |--\  |--\  |--\  |--\  |--\  |--\  |--\
		//       02 03             08
		{
			mods: []singleModify{
				// 1st modify.
				{
					[]Leaf{
						{Hash{1}, true},
						{Hash{2}, false},
						{Hash{3}, true},
						{Hash{4}, false},
						{Hash{5}, false},
						{Hash{6}, true},
						{Hash{7}, false},
						{Hash{8}, false},
					},
					nil,
				},
				// 2nd modify.
				{
					[]Leaf{
						{Hash{9}, false},
					},
					[]Hash{
						{6}, {1},
					},
				},
			},
			proves: [][]uint64{
				{2},
				{8},
				{translatePos(16, TreeRows(9), defaultForestRows)},
				{translatePos(35, TreeRows(9), defaultForestRows)},
				{2, translatePos(19, TreeRows(9), defaultForestRows)},
				{2, translatePos(16, TreeRows(9), defaultForestRows), translatePos(19, TreeRows(9), defaultForestRows)},
			},
		},

		// Creates a tree like below.
		//
		// 14
		// |-----------\
		//             13
		// |-----\     |-----\
		//       09
		// |--\  |--\  |--\  |--\
		// 01 02
		{
			mods: []singleModify{
				{
					[]Leaf{
						{Hash{1}, true},
						{Hash{2}, false},
						{Hash{3}, false},
						{Hash{4}, false},
						{Hash{5}, false},
						{Hash{6}, false},
						{Hash{7}, false},
						{Hash{8}, false},
					},
					nil,
				},
			},
			proves: [][]uint64{{0}, {1}, {0, 1}, {2}, {5}, {5, 6}},
		},
	}

	// Closure for checking that the positions from the GetMissingPositions method
	// was correct.
	sanityCheck := func(t *testing.T, p *MapPollard, proves, missing []uint64) {
		// Check that all the positions can actually exist.
		for i := range missing {
			if !inForest(missing[i], p.NumLeaves, defaultForestRows) {
				t.Fatalf("pos %d cannot exist in an accumulator with %d leaves",
					missing[i], p.NumLeaves)
			}
		}

		// Check for duplicates and turn the slice into a map for easy lookup.
		missingMap := make(map[uint64]struct{}, len(missing))
		for _, elem := range missing {
			// There might be duplicates if there was some positions that couldn't
			// exist in the accumulator as they get translated.
			_, found := missingMap[elem]
			if found {
				t.Fatalf("duplicates found in missing positions of %v", missing)
			}
			missingMap[elem] = struct{}{}
		}

		targets := copySortedFunc(proves, uint64Cmp)
		if p.TotalRows != defaultForestRows {
			targets = translatePositions(targets, defaultForestRows, p.TotalRows)
		}

		// Calculate the positions actually needed.
		needs, _ := ProofPositions(targets, p.NumLeaves, p.TotalRows)
		if defaultForestRows != p.TotalRows {
			needs = translatePositions(needs, p.TotalRows, defaultForestRows)
		}

		// Check that the missing positions are indeed missing.
		for _, need := range needs {
			if empty == p.GetHash(need) {
				// It's not in the accumulator so it should be in the
				// missing map.
				_, found := missingMap[need]
				if !found {
					t.Fatalf("%d was stated as not missing but "+
						"wasn't found in the accumulator.", need)
				}
			} else {
				// It's in the accumulator so it shouldn't be in the
				// missing map.
				_, found := missingMap[need]
				if found {
					t.Fatalf("%d was stated as missing but "+
						"it exists in the accumulator.", need)
				}
			}
		}
	}

	for i, test := range tests {
		p := NewMapPollard(false)

		for _, mod := range test.mods {
			err := applySingleModify(&p, mod.adds, mod.dels)
			if err != nil {
				t.Fatalf("failed modify on %d. %v", i, err)
			}
		}

		for _, prove := range test.proves {
			missing := p.GetMissingPositions(prove)
			sanityCheck(t, &p, prove, missing)
		}
	}
}

func TestVerifyPartialProof(t *testing.T) {
	type toProve struct {
		proveLeafHash []Hash
		proveTargets  []uint64
	}

	tests := []struct {
		mods     []singleModify
		toProves []toProve
	}{
		// Generates an accumulator like so.
		// Leaves with * appended to it are the ones that
		// are cached.
		//
		// |-----------------------\
		// 28
		// |-----------\           |-----------\
		// 24          25
		// |-----\     |-----\     |-----\     |-----\
		// 16*   17    18*   19
		// |--\  |--\  |--\  |--\  |--\  |--\  |--\  |--\
		//       02*03       06 07 08
		{
			mods: []singleModify{
				{
					[]Leaf{
						{Hash{0, 0xff}, true},
						{Hash{1, 0xff}, false},
						{Hash{2, 0xff}, true},
						{Hash{3, 0xff}, false},
						{Hash{4, 0xff}, true},
						{Hash{5, 0xff}, true},
						{Hash{6, 0xff}, false},
						{Hash{7, 0xff}, false},
					},
					nil,
				},
				{
					[]Leaf{
						{Hash{8, 0xff}, false},
					},
					[]Hash{{4, 0xff}, {0, 0xff}},
				},
			},

			toProves: []toProve{
				{
					proveLeafHash: []Hash{{7, 0xff}},
					proveTargets:  []uint64{7},
				},

				{
					proveLeafHash: []Hash{{1, 0xff}},
					proveTargets:  []uint64{16},
				},

				{
					proveLeafHash: []Hash{{2, 0xff}},
					proveTargets:  []uint64{2},
				},
			},
		},
	}

	genAcc := func(utreexo Utreexo, test []singleModify) error {
		for _, mod := range test {
			err := applySingleModify(utreexo, mod.adds, mod.dels)
			if err != nil {
				return err
			}
		}

		return nil
	}

	for _, test := range tests {
		// Create the starting off pollard.
		p := NewMapPollard(false)

		// Generate the 2 pollards.
		err := genAcc(&p, test.mods)
		if err != nil {
			t.Fatal(err)
		}
		full := NewAccumulator()
		err = genAcc(&full, test.mods)
		if err != nil {
			t.Fatal(err)
		}

		for _, toProve := range test.toProves {
			// Translate hardcoded positions to defaultForestRows for the API calls.
			apiTargets := toProve.proveTargets
			verifyTreeRows := TreeRows(p.NumLeaves)
			if verifyTreeRows != defaultForestRows {
				apiTargets = translatePositions(toProve.proveTargets, verifyTreeRows, defaultForestRows)
			}

			// Generate the missing positions of the hashes we need to
			// prove the targets.
			missing := p.GetMissingPositions(apiTargets)

			// Grab the missing hashes from the full accumulator.
			// This simulates another utreexo peer returning the missing hashes
			// after requesting for them.
			hashes := make([]Hash, len(missing))
			for i := range hashes {
				hashes[i] = full.GetHash(missing[i])
			}

			cached := true
			for _, leafHash := range toProve.proveLeafHash {
				_, found := p.Nodes.Get(leafHash)
				if !found {
					cached = false
				}
			}

			// Call VerifyPartialProof and make sure that with the given hashes,
			// we can verify the targets.
			err = p.VerifyPartialProof(apiTargets, toProve.proveLeafHash, hashes, false)
			if err != nil {
				t.Fatal(err)
			}

			_, err = p.Prove(toProve.proveLeafHash)
			if !cached && err == nil {
				t.Fatalf("Shouldn't be able to prove uncached leaf")
			}

			// Now call with remember as true.
			err = p.VerifyPartialProof(apiTargets, toProve.proveLeafHash, hashes, true)
			if err != nil {
				t.Fatal(err)
			}
			_, err = p.Prove(toProve.proveLeafHash)
			if err != nil {
				t.Fatal(err)
			}
		}
	}
}

func TestFullMapPollard(t *testing.T) {
	// Create elements to add to the accumulator
	leaves := make([]Leaf, 31)
	for i := range leaves {
		leaves[i] = Leaf{Hash: sha256.Sum256([]byte{uint8(i)}), Remember: false}
	}

	acc := NewMapPollard(true)
	err := acc.Modify(leaves, nil, Proof{})
	if err != nil {
		t.Fatal(err)
	}

	acc1 := NewMapPollard(false)
	err = acc1.Modify(leaves, nil, Proof{})
	if err != nil {
		t.Fatal(err)
	}

	proveHashes := make([]Hash, 3)
	for i := range proveHashes {
		proveHashes[i] = leaves[i].Hash
	}
	proof, err := acc.Prove(proveHashes)
	if err != nil {
		t.Fatal(err)
	}

	// Verify that it fails with the mappollard that didn't have the full as true.
	_, err = acc1.Prove(proveHashes)
	if err == nil {
		t.Fatalf("expected to fail for a map pollard without the " +
			"full flag but the error returned nil")
	}

	// Sanity check with a stump.
	addHashes := make([]Hash, len(leaves))
	for i := range leaves {
		addHashes[i] = leaves[i].Hash
	}
	stump := Stump{}
	_, err = stump.Update(nil, addHashes, Proof{})
	if err != nil {
		t.Fatal(err)
	}

	_, err = Verify(stump, proveHashes, proof)
	if err != nil {
		t.Fatal(err)
	}
}

func TestMapPollardGetLeafPosition(t *testing.T) {
	// Create elements to add to the accumulator
	leaves := make([]Leaf, 31)
	for i := range leaves {
		leaves[i] = Leaf{Hash: sha256.Sum256([]byte{uint8(i)}), Remember: false}
	}

	acc := NewMapPollard(true)
	err := acc.Modify(leaves, nil, Proof{})
	if err != nil {
		t.Fatal(err)
	}

	delLeaves := []Leaf{leaves[1]}
	delHashes := make([]Hash, len(delLeaves))
	for i := range delHashes {
		delHashes[i] = delLeaves[i].Hash
	}
	proof, err := acc.Prove(delHashes)
	if err != nil {
		t.Fatal(err)
	}

	err = acc.Modify(nil, delHashes, proof)
	if err != nil {
		t.Fatal(err)
	}

	// Actual test is here.
	expected := Parent(0, TreeRows(uint64(len(leaves))))
	got, found := acc.GetLeafPosition(leaves[0].Hash)
	if !found {
		t.Fatalf("expected to find position for hash %v but didn't", leaves[0].Hash)
	}

	if expected != got {
		t.Fatalf("for hash %v, expected %v but got %v",
			leaves[0].Hash, expected, got)
	}
}

func FuzzMapPollardTTLs(f *testing.F) {
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

		m := NewMapPollard(true)

		// Create forest with blockCountsFile for TTL tracking
		tmpDir := t.TempDir()
		forest, err := newForest(memCached(t, 32), memCached(t, 4), memCached(t, 32), nil, tmpDir+"/ctrl", tmpDir+"/slots", 16, 0)
		if err != nil {
			t.Fatal(err)
		}

		leafMap := make(map[Hash]int32, 50*numAdds)

		var totalAdds, totalDels int
		for b := 1; b <= 50; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)
			totalAdds += len(adds)
			totalDels += len(delHashes)

			for i, add := range adds {
				leafMap[add.Hash] = int32(i)
			}

			proof, err := m.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzMapPollardTTLs fail at block %d. Couldn't prove\n%s\nError: %v",
					b, printHashes(delHashes), err)
			}

			origRoots := m.GetRoots()

			createIndex, err := m.ModifyAndReturnTTLs(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("FuzzMapPollardTTLs fail at block %d. Error: %v", b, err)
			}

			// Forest should return the same addIndexes
			forestIndex, err := forest.ModifyAndReturnTTLs(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("FuzzMapPollardTTLs fail at block %d. Forest error: %v", b, err)
			}
			require.Equal(t, createIndex, forestIndex, "block %d: forest addIndexes don't match mappollard", b)

			for i, delHash := range delHashes {
				ttlInfo, found := leafMap[delHash]
				if !found {
					t.Fatalf("FuzzMapPollardTTLs fail at block %d. Expected to find delhash %v but didn't",
						b, delHash)
				}

				if createIndex[i] != ttlInfo {
					t.Fatalf("FuzzMapPollardTTLs fail at block %d. For %v, expected create index %v got %v",
						b, delHash, ttlInfo, createIndex[i])
				}
			}

			addHashes := make([]Hash, len(adds))
			for i, add := range adds {
				addHashes[i] = add.Hash
			}

			err = m.UndoWithTTLs(addHashes, createIndex, proof, delHashes, origRoots)
			if err != nil {
				t.Fatalf("FuzzMapPollardTTLs fail at block %d. Error: %v", b, err)
			}

			err = forest.Undo(addHashes, proof, delHashes, origRoots)
			if err != nil {
				t.Fatalf("FuzzMapPollardTTLs fail at block %d. Forest error: %v", b, err)
			}

			gotIndex, err := m.ModifyAndReturnTTLs(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("FuzzMapPollardTTLs fail at block %d. Error: %v", b, err)
			}

			require.Equal(t, createIndex, gotIndex)

			gotForestIndex, err := forest.ModifyAndReturnTTLs(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("FuzzMapPollardTTLs fail at block %d. Forest error: %v", b, err)
			}
			require.Equal(t, createIndex, gotForestIndex, "block %d: forest addIndexes don't match mappollard", b)
		}
	})
}

func TestSerializeSize(t *testing.T) {
	tests := []struct {
		leafCount   int
		remInterval int
	}{
		{leafCount: 0, remInterval: 0},
		{leafCount: 1524, remInterval: 1},
		{leafCount: 1524, remInterval: 2},
		{leafCount: 1524, remInterval: 5},
		{leafCount: 1524, remInterval: 9},
		{leafCount: 105487, remInterval: 1},
		{leafCount: 105487, remInterval: 2},
		{leafCount: 105487, remInterval: 5},
		{leafCount: 105487, remInterval: 14},
	}

	for _, test := range tests {
		mp := NewMapPollard(false)

		// Create elements to add to the accumulator
		leaves := make([]Leaf, test.leafCount)
		var hashBuf [8]byte
		for i := range leaves {
			binary.LittleEndian.PutUint64(hashBuf[:], uint64(i))
			leaves[i] = Leaf{Hash: sha256.Sum256(hashBuf[:])}

			if i%test.remInterval == 0 {
				leaves[i].Remember = true
			}
		}

		// Add the leaves.
		err := mp.Modify(leaves, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}

		// Grab the size calculated by serialize size.
		size := mp.SerializeSize()

		// Write to buf and grab size.
		var buf bytes.Buffer
		written, err := mp.Write(&buf)
		if err != nil {
			t.Fatal(err)
		}

		require.Equal(t, written, size)
	}

}
