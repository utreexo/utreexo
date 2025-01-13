package utreexo

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"math/rand"
	"reflect"
	"testing"

	"golang.org/x/exp/slices"
)

// Assert that MapPollard implements the UtreexoTest interface.
var _ UtreexoTest = (*MapPollard)(nil)

// cachedMapToString returns the cached map as a string.
//
// Implements the UtreexoTest interface.
func (p *MapPollard) cachedMapToString() string {
	return fmt.Sprintf("%v", p.CachedLeaves)
}

// nodeMapToString returns "n/a" as map pollard doesn't have a node map.
func (m *MapPollard) nodeMapToString() string {
	return "n/a"
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
	err := m.checkCachedNodesAreRemembered()
	if err != nil {
		return err
	}

	err = m.checkProofNodes()
	if err != nil {
		return err
	}

	err = m.checkHashes()
	if err != nil {
		return err
	}

	return m.checkPruned()
}

// checkCachedNodesAreRemembered checks that cached leaves are present in m.Nodes and that they're
// marked to be remembered.
func (m *MapPollard) checkCachedNodesAreRemembered() error {
	return m.CachedLeaves.ForEach(func(k Hash, v uint64) error {
		leaf, found := m.Nodes.Get(v)
		if !found {
			return fmt.Errorf("Cached node of %s at pos %d not cached in m.Nodes", k, v)
		}

		if leaf.Remember == false {
			return fmt.Errorf("Cached node of %s at pos %d not marked as remembered in m.Nodes", k, v)
		}

		return nil
	})
}

// checkPruned checks that unneeded nodes aren't cached.
func (m *MapPollard) checkPruned() error {
	neededPos := make(map[uint64]struct{})
	m.CachedLeaves.ForEach(func(_ Hash, v uint64) error {
		neededPos[v] = struct{}{}

		needs, computables := ProofPositions([]uint64{v}, m.NumLeaves, m.TotalRows)
		for _, need := range needs {
			neededPos[need] = struct{}{}
		}

		for _, computable := range computables {
			neededPos[computable] = struct{}{}
		}
		return nil
	})

	for _, pos := range RootPositions(m.NumLeaves, m.TotalRows) {
		neededPos[pos] = struct{}{}
	}

	return m.Nodes.ForEach(func(k uint64, v Leaf) error {
		_, found := neededPos[k]
		if !found {
			return fmt.Errorf("Have node %s at pos %d in map "+
				"even though it's not needed.\nCachedLeaves:\n%v\nm.Nodes:\n%v\n",
				v, k, m.CachedLeaves, m.Nodes)
		}

		return nil
	})
}

// checkProofNodes checks that all the proof positions needed to cache a proof exists in the map
// of nodes.
func (m *MapPollard) checkProofNodes() error {
	// Sanity check.
	return m.CachedLeaves.ForEach(func(k Hash, v uint64) error {
		leaf, found := m.Nodes.Get(v)
		if !found {
			return fmt.Errorf("Corrupted pollard. Missing cached leaf %s at %d", k, v)
		}

		if k != leaf.Hash {
			return fmt.Errorf("Corrupted pollard. Pos %d cached hash: %s, but have %s",
				v, k, leaf.Hash)
		}

		proofPos := proofPosition(v, m.NumLeaves, m.TotalRows)
		for _, pos := range proofPos {
			_, found := m.Nodes.Get(pos)
			if !found {
				return fmt.Errorf("Corrupted pollard. Missing pos %d "+
					"needed for proving %d", pos, v)
			}
		}

		return nil
	})
}

// checkHashes checks that the leaves correctly hash up to the roots. Returns an error if
// any of the roots or the intermediate nodes don't match up with the calculated hashes.
func (m *MapPollard) checkHashes() error {
	if m.CachedLeaves.Length() == 0 {
		return nil
	}

	leafHashes := make([]Hash, 0, m.CachedLeaves.Length())
	m.CachedLeaves.ForEach(func(k Hash, _ uint64) error {
		leafHashes = append(leafHashes, k)
		return nil
	})

	proof, err := m.Prove(leafHashes)
	if err != nil {
		return err
	}

	if m.TotalRows != TreeRows(m.NumLeaves) {
		for i := range proof.Targets {
			proof.Targets[i] = translatePos(proof.Targets[i], m.TotalRows, TreeRows(m.NumLeaves))
		}
	}

	haveRoots, rootPositions := m.getRoots()
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
			return fmt.Errorf("For root position %d, calculated %s but have %s",
				rootPositions[i], hex.EncodeToString(gotRoots[i][:]),
				hex.EncodeToString(haveRoots[rootIdx][:]))
		}
	}

	// Check all intermediate nodes.
	for i, pos := range intermediate.positions {
		haveNode, found := m.Nodes.Get(pos)
		if !found {
			continue
		}
		gotHash := intermediate.hashes[i]

		if haveNode.Hash != gotHash {
			return fmt.Errorf("For position %d, calculated %s but have %s",
				pos, hex.EncodeToString(gotHash[:]), hex.EncodeToString(haveNode.Hash[:]))
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

func FuzzMapPollardChain(f *testing.F) {
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
		if numAdds&1 == 1 {
			m.TotalRows = 50
		}
		full := NewAccumulator()

		var totalAdds, totalDels int
		for b := 0; b <= 50; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)
			totalAdds += len(adds)
			totalDels += len(delHashes)

			expectProof, err := full.Prove(delHashes)
			if err != nil {
				t.Fatal(err)
			}

			err = m.Verify(delHashes, expectProof, true)
			if err != nil {
				t.Fatalf("%v\nproving delHashes:\nproof:\n%s\n%s\nmap:\n%s\nfull:\n%s\n",
					err, printHashes(delHashes), expectProof.String(),
					m.String(), full.String())
			}

			proof, err := m.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzMapPollardChain fail at block %d. Couldn't prove\n%s\nError: %v",
					b, printHashes(delHashes), err)
			}

			err = proof.checkEqualProof(expectProof)
			if err != nil {
				t.Fatalf("\nFor delhashes: %v\nexpected proof:\n%s\ngot:\n%s\nerr: %v\n"+
					"maptreexo:\n%s\nfull:\n%s\n",
					printHashes(delHashes), expectProof.String(), proof.String(), err,
					m.String(), full.String())
			}

			for _, target := range proof.Targets {
				fetch := target
				if m.TotalRows != TreeRows(m.NumLeaves) {
					fetch = translatePos(fetch, TreeRows(m.NumLeaves), m.TotalRows)
				}
				hash := m.GetHash(fetch)
				if hash == empty {
					t.Fatalf("FuzzMapPollardChain doesn't have the hash "+
						"for %d at block %d.", target, b)
				}
			}

			err = m.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("FuzzMapPollardChain fail at block %d. Error: %v", b, err)
			}

			err = full.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatal(err)
			}

			cachedHashes := make([]Hash, 0, m.CachedLeaves.Length())
			leafHashes := make([]Hash, 0, m.CachedLeaves.Length())
			m.CachedLeaves.ForEach(func(k Hash, _ uint64) error {
				cachedHashes = append(cachedHashes, k)
				leafHashes = append(leafHashes, k)
				return nil
			})

			if !reflect.DeepEqual(cachedHashes, leafHashes) {
				err := fmt.Errorf("Fail at block %d. For cachedLeaves of %v\ngot cachedHashes:\n%s\n"+
					"leafHashes:\n%s\nmaptreexo:\n%s\nfull:\n%s\n",
					b, m.CachedLeaves, printHashes(cachedHashes), printHashes(leafHashes),
					m.String(), full.String())
				t.Fatal(err)
			}

			cachedProofExpect, err := full.Prove(cachedHashes)
			if err != nil {
				t.Fatal(err)
			}

			cachedProof, err := m.Prove(leafHashes)
			if err != nil {
				t.Fatal(err)
			}

			if m.TotalRows != TreeRows(m.NumLeaves) {
				for i := range cachedProof.Targets {
					cachedProof.Targets[i] = translatePos(
						cachedProof.Targets[i], m.TotalRows, TreeRows(m.NumLeaves))
				}
			}

			err = cachedProof.checkEqualProof(cachedProofExpect)
			if err != nil {
				t.Fatalf("\nFor delhashes: %v\nexpected proof:\n%s\ngot:\n%s\nerr: %v\n"+
					"maptreexo:\n%s\nfull:\n%s\n",
					printHashes(cachedHashes), cachedProofExpect.String(), cachedProof.String(),
					err, m.String(), full.String())
			}

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

		rand.Seed(seed)

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

		// Return now since we don't have anything to prune.
		if acc.CachedLeaves.Length() == 0 {
			return
		}

		// Randomly choose targets to prune.
		count := rand.Intn(acc.CachedLeaves.Length())
		prunedPositions := make([]uint64, 0, count)
		targets := make([]uint64, 0, acc.CachedLeaves.Length())

		toPrune := make([]Hash, 0, count)
		notPruned := make([]Hash, 0, acc.CachedLeaves.Length()-count)
		acc.CachedLeaves.ForEach(func(k Hash, v uint64) error {
			if len(toPrune) >= count {
				targets = append(targets, v)
				notPruned = append(notPruned, k)
				return nil
			}
			if rand.Int()%2 == 0 {
				toPrune = append(toPrune, k)
				prunedPositions = append(prunedPositions, v)
			} else {
				targets = append(targets, v)
				notPruned = append(notPruned, k)
			}

			return nil
		})
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
			_, found := acc.Nodes.Get(pos)
			if found {
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
			proves: [][]uint64{{2}, {8}, {16}, {35}, {2, 19}, {2, 16, 19}},
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
			if !inForest(missing[i], p.NumLeaves, TreeRows(p.NumLeaves)) {
				t.Fatalf("pos %d cannot exist in an accumulator with %d leaves",
					missing[i], p.NumLeaves)
			}
		}

		// Translate if needed.
		if TreeRows(p.NumLeaves) != p.TotalRows {
			missing = translatePositions(missing, TreeRows(p.NumLeaves), p.TotalRows)
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

		// Calculate the positions actually needed.
		needs, _ := ProofPositions(proves, p.NumLeaves, TreeRows(p.NumLeaves))
		if TreeRows(p.NumLeaves) != p.TotalRows {
			needs = translatePositions(needs, TreeRows(p.NumLeaves), p.TotalRows)
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
			// Generate the missing positions of the hashes we need to
			// prove the targets.
			missing := p.GetMissingPositions(toProve.proveTargets)

			// Grab the missing hashes from the full accumulator.
			// This simulates another utreexo peer returning the missing hashes
			// after requesting for them.
			hashes := make([]Hash, len(missing))
			for i := range hashes {
				hashes[i] = full.GetHash(missing[i])
			}

			cached := true
			for _, leafHash := range toProve.proveLeafHash {
				_, found := p.CachedLeaves.Get(leafHash)
				if !found {
					cached = false
				}
			}

			// Call VerifyPartialProof and make sure that with the given hashes,
			// we can verify the targets.
			err = p.VerifyPartialProof(toProve.proveTargets, toProve.proveLeafHash, hashes, false)
			if err != nil {
				t.Fatal(err)
			}

			_, err = p.Prove(toProve.proveLeafHash)
			if !cached && err == nil {
				t.Fatalf("Shouldn't be able to prove uncached leaf")
			}

			// Now call with remember as true.
			err = p.VerifyPartialProof(toProve.proveTargets, toProve.proveLeafHash, hashes, true)
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

func TestGetLeafHashPositions(t *testing.T) {
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
	expected := parent(0, TreeRows(uint64(len(leaves))))
	got, found := acc.getLeafHashPosition(leaves[0].Hash)
	if !found {
		t.Fatalf("expected to find position for hash %v but didn't", leaves[0].Hash)
	}

	if expected != got {
		t.Fatalf("for hash %v, expected %v but got %v",
			leaves[0].Hash, expected, got)
	}
}
