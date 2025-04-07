package utreexo

import (
	"fmt"
	"math/rand"
	"reflect"
	"sort"
	"testing"

	"github.com/stretchr/testify/require"
	"golang.org/x/exp/slices"
)

// Grab some random indexes. If minimum is greater than length, nil is returned.
func randomIndexes(length, minimum int) []int {
	if minimum > length {
		return nil
	}
	indexes := []int{}

	// Optimization for when the caller wants everything.
	if minimum == length {
		indexes = make([]int, length)
		for i := range indexes {
			indexes[i] = i
		}

		return indexes
	}

	// Loop until we get enough.
	for len(indexes) < minimum {
		// Reset the slice first.
		indexes = indexes[:0]

		i := rand.Intn(length)
		max := length - 1
		for i <= max {
			indexes = append(indexes, i)
			if max-i <= 0 {
				break
			}
			increment := (rand.Intn(max-i) + i)
			if increment == 0 {
				increment++
			}
			i += increment
		}
	}

	return indexes
}

// calcDelHashAndProof returns a proof with the missingPositions filled in and the deletion hashes
// with the hashes of the desired positions.
func calcDelHashAndProof(p *Pollard, proof Proof, missingPositions, desiredPositions []uint64,
	leftOutLeaves, leaves hashAndPos) (Proof, []Hash, error) {

	// Grab all the hashes that are needed from the pollard.
	neededHashes := hashAndPos{}
	sort.Slice(missingPositions, func(a, b int) bool { return missingPositions[a] < missingPositions[b] })
	for _, pos := range missingPositions {
		hash := p.getHash(pos)
		if hash == empty {
			return Proof{}, nil, fmt.Errorf("Couldn't fetch required hash at position %d", pos)
		}

		neededHashes.Append(pos, hash)
	}

	// Attach positions to the proof hashes.
	proofPos, _ := ProofPositions(proof.Targets, p.NumLeaves, TreeRows(p.NumLeaves))
	currentHashes := toHashAndPos(proofPos, proof.Proof)
	// Append the needed hashes to the proof.
	currentHashes.AppendMany(neededHashes.positions, neededHashes.hashes)

	// As new targets are added, we're able to calulate positions that we couldn't before. These positions
	// may already exist as proofs. Remove these as duplicates are not expected during proof verification.
	_, calculateables := ProofPositions(desiredPositions, p.NumLeaves, TreeRows(p.NumLeaves))
	for _, cal := range calculateables {
		idx := slices.IndexFunc(currentHashes.positions, func(elem uint64) bool { return elem == cal })
		if idx != -1 {
			currentHashes.Delete(idx)
		}
	}

	// The newly added targets may be used as proofs. Remove existing duplicates from the proof as these
	// are not expected during proof verification.
	for _, leaf := range leftOutLeaves.hashes {
		idx := slices.IndexFunc(currentHashes.hashes, func(elem Hash) bool { return elem == leaf })
		if idx != -1 {
			currentHashes.Delete(idx)
		}
	}

	// Create the proof.
	newProof := Proof{Targets: append(proof.Targets, desiredPositions...)}
	// Sort the targets as it needs to match the ordering of the deletion hashes and
	// the deletions hashes will also be sorted.
	sort.Slice(newProof.Targets, func(a, b int) bool { return newProof.Targets[a] < newProof.Targets[b] })

	// We need to sort the proof hashes as those are expected to be in order during proof verificatin.
	sort.Sort(currentHashes)
	newProof.Proof = currentHashes.hashes

	// The deletion hashes are leaves + leftOutLeaves. We sort them to match the ordering of the targets.
	leaves.AppendMany(leftOutLeaves.positions, leftOutLeaves.hashes)
	sort.Sort(leaves)

	return newProof, leaves.hashes, nil
}

func FuzzGetMissingPositions(f *testing.F) {
	var tests = []struct {
		startLeaves uint32
		delCount    uint32
		seed        int64
	}{
		{
			8,
			3,
			17,
		},
		{
			6,
			3,
			12,
		},
	}
	for _, test := range tests {
		f.Add(test.startLeaves, test.delCount, test.seed)
	}

	f.Fuzz(func(t *testing.T, startLeaves uint32, delCount uint32, seed int64) {
		t.Parallel()

		rand.Seed(seed)

		// It'll error out if we try to delete more than we have. >= since we want
		// at least 2 leftOver leaf to test.
		if int(delCount) >= int(startLeaves)-2 {
			return
		}

		// Create the starting off pollard.
		p := NewAccumulator()
		leaves, delHashes, delPos := getAddsAndDels(uint32(p.NumLeaves), startLeaves, delCount)
		err := p.Modify(leaves, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}
		err = p.Modify(nil, delHashes, Proof{Targets: delPos})
		if err != nil {
			t.Fatal(err)
		}

		// Grab the current leaves that exist in the accumulator.
		currentLeaves := hashAndPos{make([]uint64, 0, len(leaves)-len(delHashes)), make([]Hash, 0, len(leaves)-len(delHashes))}
		for _, node := range p.NodeMap {
			currentLeaves.Append(p.calculatePosition(node), node.data)
		}
		// Sort to have a deterministic order of the currentLeaves. Since maps aren't
		// guaranteed to have the same order, we need to do this.
		sort.Sort(currentLeaves)

		// Sanity check.
		if currentLeaves.Len() != len(leaves)-len(delHashes) {
			t.Fatalf("FuzzGetMissingPositions fail. Expected %d leaves but have %d in the pollard map",
				len(leaves)-len(delHashes), currentLeaves.Len())
		}

		// Randomly grab some leaves.
		indexes := randomIndexes(currentLeaves.Len(), 2)
		leafSubset := hashAndPos{make([]uint64, 0, len(indexes)), make([]Hash, 0, len(indexes))}
		for i := 0; i < len(indexes); i++ {
			leafSubset.Append(currentLeaves.positions[indexes[i]],
				currentLeaves.hashes[indexes[i]])
		}

		// Grab at least 1 leaf to leave out.
		leaveOutCount := rand.Intn(leafSubset.Len()-1) + 1
		for leaveOutCount <= leafSubset.Len()-1 && leaveOutCount < 1 {
			leaveOutCount++
		}
		// Randomly select leaves to leave out.
		leftOutLeaves := hashAndPos{make([]uint64, 0, leaveOutCount), make([]Hash, 0, leaveOutCount)}
		for i := 0; i < leaveOutCount; i++ {
			// Randomly select a leaf to leave out.
			hashIdx := rand.Intn(leafSubset.Len() - 1)
			leftOutLeaves.Append(leafSubset.positions[hashIdx], leafSubset.hashes[hashIdx])

			// Remove the selected leaf from the subset.
			leafSubset.Delete(hashIdx)
		}

		// Grab the proof of the leaves that we didn't leave out.
		proof, err := p.Prove(leafSubset.hashes)
		if err != nil {
			t.Fatal(err)
		}

		// Grab the positions of the leaves that we left out.
		desiredPositions := make([]uint64, leftOutLeaves.Len())
		copy(desiredPositions, leftOutLeaves.positions)

		// Call GetMissingPositions and get all the positions that we need to prove desiredPositions.
		missingPositions := GetMissingPositions(p.NumLeaves, proof.Targets, desiredPositions)

		// Create a new proof from missingPositions and verify to make sure it's correct.
		newProof, newDelHashes, err := calcDelHashAndProof(&p, proof, missingPositions, desiredPositions, leftOutLeaves, leafSubset)
		if err != nil {
			t.Fatalf("FuzzGetMissingPositions fail. Error %v", err)
		}
		err = p.Verify(newDelHashes, newProof, false)
		if err != nil {
			t.Fatalf("FuzzGetMissingPositions fail: New proof failed to verify. error: %v", err)
		}
	})
}

func FuzzAddProof(f *testing.F) {
	var tests = []struct {
		startLeaves uint32
		delCount    uint32
		seed        int64
	}{
		{
			16,
			2,
			12,
		},
	}
	for _, test := range tests {
		f.Add(test.startLeaves, test.delCount, test.seed)
	}

	f.Fuzz(func(t *testing.T, startLeaves uint32, delCount uint32, seed int64) {
		t.Parallel()

		rand.Seed(seed)

		// It'll error out if we try to delete more than we have. >= since we want
		// at least 2 leftOver leaf to test.
		if int(delCount) >= int(startLeaves)-2 {
			return
		}

		// Get leaves and dels.
		leaves, delHashes, delPos := getAddsAndDels(0, startLeaves, delCount)

		// Create the starting off pollard.
		p := NewAccumulator()
		err := p.Modify(leaves, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}
		err = p.Modify(nil, delHashes, Proof{Targets: delPos})
		if err != nil {
			t.Fatal(err)
		}

		// Grab the current leaves that exist in the accumulator.
		currentLeaves := hashAndPos{make([]uint64, 0, len(leaves)-len(delHashes)), make([]Hash, 0, len(leaves)-len(delHashes))}
		for _, node := range p.NodeMap {
			currentLeaves.Append(p.calculatePosition(node), node.data)
		}
		// Sort to have a deterministic order of the currentLeaves. Since maps aren't
		// guaranteed to have the same order, we need to do this.
		sort.Sort(currentLeaves)

		// Randomly grab some leaves.
		indexesA := randomIndexes(currentLeaves.Len(), 2)
		leafSubsetA := hashAndPos{make([]uint64, 0, len(indexesA)), make([]Hash, 0, len(indexesA))}
		for _, idx := range indexesA {
			leafSubsetA.Append(currentLeaves.positions[idx], currentLeaves.hashes[idx])
		}

		indexesB := randomIndexes(currentLeaves.Len(), 2)
		leafSubsetB := hashAndPos{make([]uint64, 0, len(indexesB)), make([]Hash, 0, len(indexesB))}
		for _, idx := range indexesB {
			leafSubsetB.Append(currentLeaves.positions[idx], currentLeaves.hashes[idx])
		}

		// Generate a proof of the leafSubset.
		proofA, err := p.Prove(leafSubsetA.hashes)
		if err != nil {
			t.Fatal(err)
		}

		proofB, err := p.Prove(leafSubsetB.hashes)
		if err != nil {
			t.Fatal(err)
		}

		// Add the proof.
		leafHashesC, proofC := AddProof(proofA, proofB, leafSubsetA.hashes, leafSubsetB.hashes, p.NumLeaves)

		// These are the targets that we want to prove.
		sortedProofATargets := copySortedFunc(proofA.Targets, uint64Cmp)
		sortedProofBTargets := copySortedFunc(proofB.Targets, uint64Cmp)
		expectedTargets := mergeSortedSlicesFunc(sortedProofATargets, sortedProofBTargets, uint64Cmp)

		// This is the targets that we got from AddProof.
		sortedProofCTargets := copySortedFunc(proofC.Targets, uint64Cmp)

		// When we subtract the slice, we should get nothing since sortedProofCTargets and expectedTargets should
		// be the same.
		shouldBeEmpty := subtractSortedSlice(sortedProofCTargets, expectedTargets, uint64Cmp)
		if len(shouldBeEmpty) > 0 {
			t.Fatalf("FuzzAddProof Fail. Not all wanted targets were added. Expected %v, got %v",
				expectedTargets, proofC.Targets)
		}

		// Check that the proof verifies.
		err = p.Verify(leafHashesC, proofC, false)
		if err != nil {
			t.Fatal(err)
		}
	})
}

func FuzzUpdateProofRemove(f *testing.F) {
	var tests = []struct {
		startLeaves uint32
		delCount    uint32
		seed        int64
	}{
		{
			16,
			2,
			12,
		},
	}
	for _, test := range tests {
		f.Add(test.startLeaves, test.delCount, test.seed)
	}

	f.Fuzz(func(t *testing.T, startLeaves uint32, delCount uint32, seed int64) {
		t.Parallel()

		rand.Seed(seed)

		// It'll error out if we try to delete more than we have. >= since we want
		// at least 2 leftOver leaf to test.
		if int(delCount) >= int(startLeaves)-2 {
			return
		}

		// Get leaves and dels.
		leaves, delHashes, delPos := getAddsAndDels(0, startLeaves, delCount)

		// Create the starting off pollard.
		p := NewAccumulator()
		err := p.Modify(leaves, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}
		err = p.Modify(nil, delHashes, Proof{Targets: delPos})
		if err != nil {
			t.Fatal(err)
		}
		pollardBeforeStr := p.String()

		// Grab the current leaves that exist in the accumulator.
		currentLeaves := hashAndPos{make([]uint64, 0, len(leaves)-len(delHashes)), make([]Hash, 0, len(leaves)-len(delHashes))}
		for _, node := range p.NodeMap {
			currentLeaves.Append(p.calculatePosition(node), node.data)
		}
		// Sort to have a deterministic order of the currentLeaves. Since maps aren't
		// guaranteed to have the same order, we need to do this.
		sort.Sort(currentLeaves)

		// Randomly grab some leaves.
		indexes := randomIndexes(currentLeaves.Len(), 2)
		leafSubset := hashAndPos{make([]uint64, 0, len(indexes)), make([]Hash, 0, len(indexes))}
		for i := 0; i < len(indexes); i++ {
			leafSubset.Append(currentLeaves.positions[indexes[i]],
				currentLeaves.hashes[indexes[i]])
		}
		// Generate a proof of the leafSubset.
		cachedProof, err := p.Prove(leafSubset.hashes)
		if err != nil {
			t.Fatal(err)
		}

		// Randomly generate some positions to delete.
		delIndexes := randomIndexes(currentLeaves.Len(), 1)
		delPositions := make([]uint64, len(delIndexes))
		for i := range delIndexes {
			delPositions[i] = currentLeaves.positions[delIndexes[i]]
		}

		// Fetch hashes.
		blockDelHashes := make([]Hash, len(delPositions))
		for i := range blockDelHashes {
			blockDelHashes[i] = p.getHash(delPositions[i])
			if blockDelHashes[i] == empty {
				t.Fatal("FuzzUpdateProofRemove Fail. Couldn't fetch hash for position", delPositions[i])
			}
		}

		// Generate the proof of the targets being deleted.
		blockProof, err := p.Prove(blockDelHashes)
		if err != nil {
			t.Fatal(err)
		}

		// origTargetsAndHash is only for the error message.
		origTargetsAndHash := toHashAndPos(cachedProof.Targets, leafSubset.hashes)

		// Delete the block hashes from the cached hashes. We'll use this to make
		// sure that the proof proves what we want to prove.
		cachedTargetsAndHash := toHashAndPos(cachedProof.Targets, leafSubset.hashes)
		blockDelTargetsAndHash := toHashAndPos(blockProof.Targets, blockDelHashes)
		cachedTargetsAndHash = subtractSortedHashAndPos(cachedTargetsAndHash, blockDelTargetsAndHash.positions, uint64Cmp)

		// Update the cached proof with the block proof.
		updated, _, err := calculateHashes(p.NumLeaves, nil, blockProof)
		if err != nil {
			t.Fatal(err)
		}
		leafSubset.hashes = cachedProof.updateProofRemove(blockProof.Targets, leafSubset.hashes, updated, p.NumLeaves)

		// Modify the pollard.
		err = p.Modify(nil, blockDelHashes, Proof{Targets: delPositions})
		if err != nil {
			t.Fatal(err)
		}

		// Check that we have enough targets as we expect.
		if len(cachedProof.Targets) != cachedTargetsAndHash.Len() {
			t.Fatalf("FuzzUpdateProofRemove Fail. Expected %d targets but got %d."+
				"\nDeleted targets:\n%v.\nOriginal cached targets:\n%v\nExpected old targets:\n%v\n"+
				"Got targets:\n%v\nPollard before:\n%s\nPollard after:\n%s\n",
				cachedTargetsAndHash.Len(), len(cachedProof.Targets), blockProof.Targets,
				origTargetsAndHash.String(), cachedTargetsAndHash.String(),
				cachedProof.Targets, pollardBeforeStr, p.String())
		}

		shouldBeEmpty := hashAndPos{make([]uint64, cachedTargetsAndHash.Len()), make([]Hash, cachedTargetsAndHash.Len())}
		copy(shouldBeEmpty.positions, cachedTargetsAndHash.positions)
		copy(shouldBeEmpty.hashes, cachedTargetsAndHash.hashes)
		leafHashesAndPos := toHashAndPos(cachedProof.Targets, leafSubset.hashes)

		// Check that all the hashes we expect to be cached are all there.
		shouldBeEmpty = removeHashesFromHashAndPos(shouldBeEmpty, leafHashesAndPos.hashes, func(elem Hash) Hash { return elem })
		if shouldBeEmpty.Len() > 0 {
			t.Fatalf("FuzzUpdateProofRemove Fail. Expected hashes:\n%s\nbut got:\n%s\n"+
				"Pollard before:\n%s\nPollard after:\n%s\n",
				printHashes(cachedTargetsAndHash.hashes), printHashes(shouldBeEmpty.hashes),
				pollardBeforeStr, p.String())
		}

		cachedProofPos, _ := ProofPositions(cachedProof.Targets, p.NumLeaves, TreeRows(p.NumLeaves))
		if len(cachedProofPos) != len(cachedProof.Proof) {
			t.Fatalf("FuzzUpdateProofRemove Fail. CachedProof has these hashes:\n%v\n"+
				"for these targets:\n%v\n"+
				"but want hashes of these positions:\n%v.\nOriginal cached targets:\n%s\n"+
				"Pollard before:\n%s\nPollard after:\n%s\n",
				printHashes(cachedProof.Proof), cachedProof.Targets, cachedProofPos,
				origTargetsAndHash.String(),
				pollardBeforeStr, p.String())
		}

		// And verify that the proof is correct.
		err = p.Verify(leafSubset.hashes, cachedProof, false)
		if err != nil {
			t.Fatalf("FuzzUpdateProofRemove Fail\nErr: %s\n\n"+
				"Proof:\n%s\nTarget hashes:\n%s\n"+
				"Pollard before:\n%s\nPollard after:\n%s\n", err,
				cachedProof.String(), printHashes(leafSubset.hashes),
				pollardBeforeStr, p.String())
		}
	})
}

func FuzzUpdateProofAdd(f *testing.F) {
	var tests = []struct {
		startLeaves uint32
		delCount    uint32
		addCount    uint32
		seed        int64
	}{
		{
			16,
			3,
			2,
			12,
		},
	}
	for _, test := range tests {
		f.Add(test.startLeaves, test.delCount, test.addCount, test.seed)
	}

	f.Fuzz(func(t *testing.T, startLeaves, delCount, addCount uint32, seed int64) {
		t.Parallel()

		rand.Seed(seed)

		// It'll error out if we try to delete more than we have. >= since we want
		// at least 2 leftOver leaf to test.
		if int(delCount) >= int(startLeaves)-2 {
			return
		}

		// Get leaves and dels.
		leaves, delHashes, delPos := getAddsAndDels(0, startLeaves, delCount)

		// Create the starting off pollard.
		p := NewAccumulator()
		err := p.Modify(leaves, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}
		err = p.Modify(nil, delHashes, Proof{Targets: delPos})
		if err != nil {
			t.Fatal(err)
		}

		// Grab the current leaves that exist in the accumulator.
		currentLeaves := hashAndPos{make([]uint64, 0, len(leaves)), make([]Hash, 0, len(leaves))}
		for _, node := range p.NodeMap {
			currentLeaves.Append(p.calculatePosition(node), node.data)
		}
		// Sort to have a deterministic order of the currentLeaves. Since maps aren't
		// guaranteed to have the same order, we need to do this.
		sort.Sort(currentLeaves)

		// Randomly grab some leaves.
		indexes := randomIndexes(currentLeaves.Len(), 2)
		leafSubset := hashAndPos{make([]uint64, 0, len(indexes)), make([]Hash, 0, len(indexes))}
		for i := 0; i < len(indexes); i++ {
			leafSubset.Append(currentLeaves.positions[indexes[i]],
				currentLeaves.hashes[indexes[i]])
		}
		// Generate a proof of the leafSubset.
		cachedProof, err := p.Prove(leafSubset.hashes)
		if err != nil {
			t.Fatal(err)
		}

		addLeaves, _, _ := getAddsAndDels(uint32(p.NumLeaves), addCount, 0)

		// Update the cached proof with the block proof.
		addHashes := make([]Hash, len(addLeaves))
		for i, leaf := range addLeaves {
			addHashes[i] = leaf.Hash
		}
		rootHashes := make([]Hash, len(p.Roots))
		for i, root := range p.Roots {
			rootHashes[i] = root.data
		}
		proofBeforeStr := cachedProof.String()

		// Modify the stump and grab all the positions and hashes used to calculate the
		// new roots.
		rootHashesCopy := make([]Hash, len(rootHashes))
		copy(rootHashesCopy, rootHashes)
		stump := Stump{rootHashesCopy, p.NumLeaves}
		newHashes, newPositions, toDestroy := stump.add(addHashes)
		newNodes := hashAndPos{newPositions, newHashes}

		leafSubset.hashes = cachedProof.updateProofAdd(addHashes, leafSubset.hashes, nil, newNodes, p.NumLeaves, toDestroy)

		beforePollardStr := p.String()
		// Modify the pollard.
		err = p.Modify(addLeaves, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}
		afterPollardStr := p.String()

		// And verify that the proof is correct.
		err = p.Verify(leafSubset.hashes, cachedProof, false)
		if err != nil {
			t.Fatalf("FuzzUpdateProofAdd Fail. Error:\n%v\nleafHashes:\n%s\nProof before:\n%s\n"+
				"Proof:\n%s\nPollard before:\n%s\nPollard after:\n%s\n",
				err, printHashes(leafSubset.hashes), proofBeforeStr, cachedProof.String(),
				beforePollardStr, afterPollardStr)
		}
	})
}

func FuzzModifyProofChain(f *testing.F) {
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

		p := NewAccumulator()
		stump := Stump{}

		// We'll store the cached utxos here. This would be the equivalent
		// of a wallet storing its own utxos.
		var cachedProof Proof
		var cachedHashes []Hash
		for b := 0; b <= 25; b++ {
			adds, duration, delHashes := sc.NextBlock(numAdds)

			// The blockProof is the proof for the utxos being
			// spent/deleted.
			blockProof, err := p.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzModifyProof fail at block %d. Error: %v", b, err)
			}

			// Sanity checking.
			err = p.Verify(delHashes, blockProof, false)
			if err != nil {
				t.Fatal(err)
			}

			// Sanity checking.
			for _, target := range blockProof.Targets {
				n, _, _, err := p.getNode(target)
				if err != nil {
					t.Fatalf("FuzzModifyProof fail at block %d. Error: %v", b, err)
				}
				if n == nil {
					t.Fatalf("FuzzModifyProof fail to read %d at block %d.", target, b)
				}
			}

			// For logging.
			origCachedHashes := make([]Hash, len(cachedHashes))
			copy(origCachedHashes, cachedHashes)

			// Cache new utxos that have a duration longer than 3.
			var remembers []uint32
			var newHashesToCache []Hash
			for i, add := range adds {
				if duration[i] > 3 {
					remembers = append(remembers, uint32(i))
					newHashesToCache = append(newHashesToCache, add.Hash)
				}
			}

			// expectedCachedHashes is the expected hashes after the
			// modify has happened.
			expectedCachedHashes := make([]Hash, len(cachedHashes))
			copy(expectedCachedHashes, cachedHashes)
			expectedCachedHashes = removeHashes(expectedCachedHashes, delHashes, func(elem Hash) Hash { return elem })
			expectedCachedHashes = append(expectedCachedHashes, newHashesToCache...)

			// Update the proof with the deletions and additions that
			// happen in this block.
			rootHashes := make([]Hash, len(p.Roots))
			for i := range rootHashes {
				rootHashes[i] = p.Roots[i].data
			}
			addHashes := make([]Hash, len(adds))
			for i := range addHashes {
				addHashes[i] = adds[i].Hash
			}

			err = p.Modify(adds, delHashes, blockProof)
			if err != nil {
				t.Fatalf("FuzzModifyProof fail at block %d. Error: %v", b, err)
			}

			err = p.Undo(uint64(len(adds)), blockProof, delHashes, stump.Roots)
			if err != nil {
				t.Fatalf("FuzzModifyProof fail at block %d. Error: %v", b, err)
			}

			updateData, err := stump.Update(delHashes, addHashes, blockProof)
			if err != nil {
				t.Fatal(err)
			}

			cachedHashes, err = cachedProof.Update(cachedHashes, addHashes, blockProof.Targets, remembers, updateData)
			if err != nil {
				t.Fatal(err)
			}

			// Check that we have enough targets as we expect.
			if len(cachedProof.Targets) != len(cachedHashes) {
				t.Fatalf("FuzzUpdateProofRemove Fail. Expected %d "+
					"targets but got %d.\nDeleted hashes:\n%v"+
					"\nOriginal cached hashes:\n%v\nExpected "+
					"hashes:\n%v\nGot hashes:\n%v\n",
					len(cachedHashes),
					len(cachedProof.Targets),
					printHashes(delHashes),
					printHashes(origCachedHashes),
					printHashes(expectedCachedHashes),
					printHashes(cachedHashes))
			}

			shouldBeEmpty := make([]Hash, len(cachedHashes))
			copy(shouldBeEmpty, cachedHashes)

			// Check that all the hashes we expect to be cached are all there.
			shouldBeEmpty = removeHashes(shouldBeEmpty, cachedHashes, func(elem Hash) Hash { return elem })
			if len(shouldBeEmpty) > 0 {
				t.Fatalf("FuzzUpdateProofRemove Fail. Expected hashes:\n%s\nbut got:\n%s\n",
					printHashes(expectedCachedHashes), printHashes(cachedHashes))
			}
			err = p.Modify(adds, delHashes, blockProof)
			if err != nil {
				t.Fatalf("FuzzModifyProof fail at block %d. Error: %v", b, err)
			}

			// Sanity check that the modified proof verifies with the
			// modified pollard.
			err = p.Verify(cachedHashes, cachedProof, false)
			if err != nil {
				t.Fatalf("FuzzModifyProof fail at block %d. Error: %v", b, err)
			}

			_, err = Verify(stump, cachedHashes, cachedProof)
			if err != nil {
				t.Fatalf("FuzzModifyProof fail at block %d. Error: %v", b, err)
			}

			// Sanity checking.
			if b%10 == 0 {
				err = p.checkHashes()
				if err != nil {
					t.Fatal(err)
				}
			}

			err = p.posMapSanity()
			if err != nil {
				t.Fatalf("FuzzModifyProof fail at block %d. Error: %v",
					b, err)
			}
			if uint64(len(p.NodeMap)) != p.NumLeaves-p.NumDels {
				err := fmt.Errorf("FuzzModifyProof fail at block %d: "+
					"have %d leaves in map but only %d leaves in total",
					b, len(p.NodeMap), p.NumLeaves-p.NumDels)
				t.Fatal(err)
			}
		}
	})
}

func FuzzGetProofSubset(f *testing.F) {
	var tests = []struct {
		startLeaves uint32
		delCount    uint32
		seed        int64
	}{
		{
			16,
			2,
			12,
		},
	}
	for _, test := range tests {
		f.Add(test.startLeaves, test.delCount, test.seed)
	}

	f.Fuzz(func(t *testing.T, startLeaves uint32, delCount uint32, seed int64) {
		t.Parallel()

		rand.Seed(seed)

		// It'll error out if we try to delete more than we have. >= since we want
		// at least 3 leftOver leaf to test.
		if int(delCount) >= int(startLeaves)-3 {
			return
		}

		// Get leaves and dels.
		leaves, delHashes, delPos := getAddsAndDels(0, startLeaves, delCount)

		// Create the starting off pollard.
		p := NewAccumulator()
		err := p.Modify(leaves, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}
		err = p.Modify(nil, delHashes, Proof{Targets: delPos})
		if err != nil {
			t.Fatal(err)
		}

		// Grab the current leaves that exist in the accumulator.
		currentLeaves := hashAndPos{make([]uint64, 0, len(leaves)-len(delHashes)), make([]Hash, 0, len(leaves)-len(delHashes))}
		for _, node := range p.NodeMap {
			currentLeaves.Append(p.calculatePosition(node), node.data)
		}
		// Sort to have a deterministic order of the currentLeaves. Since maps aren't
		// guaranteed to have the same order, we need to do this.
		sort.Sort(currentLeaves)

		// Randomly grab some leaves.
		indexes := randomIndexes(currentLeaves.Len(), 3)
		leafSubset := hashAndPos{make([]uint64, 0, len(indexes)-1), make([]Hash, 0, len(indexes)-1)}
		for i := 0; i < len(indexes)-1; i++ {
			leafSubset.Append(currentLeaves.positions[indexes[i]],
				currentLeaves.hashes[indexes[i]])
		}
		// The last element is to test if an error indeed returns when trying to
		// prove something that's not in the cachedProof.
		excluded := []uint64{currentLeaves.positions[indexes[len(indexes)-1]]}

		// Generate a proof of the leafSubset.
		cachedProof, err := p.Prove(leafSubset.hashes)
		if err != nil {
			t.Fatal(err)
		}
		// And verify that the proof is correct.
		err = p.Verify(leafSubset.hashes, cachedProof, false)
		if err != nil {
			t.Fatal(err)
		}

		// Try to trigger an error by proving something that's not included in the cachedProof.
		_, _, err = GetProofSubset(cachedProof, leafSubset.hashes, excluded, p.NumLeaves)
		if err == nil {
			t.Fatalf("Expected an error when trying to get a proof subset of %v from %v",
				excluded, cachedProof.Targets)
		}

		// Store a copy of the cachedProof to later assert that the proof wasn't mutated.
		cachedProofCopy := Proof{make([]uint64, len(cachedProof.Targets)), make([]Hash, len(cachedProof.Proof))}
		copy(cachedProofCopy.Targets, cachedProof.Targets)
		copy(cachedProofCopy.Proof, cachedProof.Proof)

		// Store a copy of the leafSubset.hashes to later assert that the proof wasn't mutated.
		leafSubsetHashesCopy := make([]Hash, len(leafSubset.hashes))
		copy(leafSubsetHashesCopy, leafSubset.hashes)

		// Randomly generate some positions to selectively prove.
		proveIndexes := randomIndexes(leafSubset.Len(), 1)
		provePositions := make([]uint64, len(proveIndexes))
		for i := range proveIndexes {
			provePositions[i] = leafSubset.positions[proveIndexes[i]]
		}

		// Get the proof subset.
		subsetHashes, subsetProof, err := GetProofSubset(cachedProof, leafSubset.hashes, provePositions, p.NumLeaves)
		if err != nil {
			t.Fatal(err)
		}

		// Check that all the proves we want are there.
		expectedEmpty := copySortedFunc(provePositions, uint64Cmp)
		expectedEmpty = subtractSortedSlice(expectedEmpty, subsetProof.Targets, uint64Cmp)
		if len(expectedEmpty) > 0 {
			t.Fatalf("Positions %v did not get proven. All wanted positions: %v",
				expectedEmpty, provePositions)
		}

		// Verify the proof.
		err = p.Verify(subsetHashes, subsetProof, false)
		if err != nil {
			t.Fatal(err)
		}

		// Check that the cached proof and hashes were not mutated.
		if !reflect.DeepEqual(cachedProofCopy, cachedProof) {
			err := fmt.Errorf("cachedProof was mutated. Expected:\n%s\nGot:\n%s\n",
				cachedProofCopy.String(), cachedProof.String())
			t.Fatal(err)
		}
		if !reflect.DeepEqual(leafSubsetHashesCopy, leafSubset.hashes) {
			err := fmt.Errorf("leafSubset.hashes were mutated. Expected:\n%s\nGot:\n%s\n",
				printHashes(leafSubsetHashesCopy), printHashes(leafSubset.hashes))
			t.Fatal(err)
		}
	})
}

func FuzzUndoProofChain(f *testing.F) {
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

		p := NewAccumulator()
		stump := Stump{}

		undoData := []struct {
			addHashes  []Hash
			delHashes  []Hash
			targets    []uint64
			remembers  []uint32
			updateData UpdateData
			proof      Proof
			roots      []Hash

			blockHeight int
		}{}
		// We'll store the cached utxos here. This would be the equivalent
		// of a wallet storing its own utxos.
		var cachedProof Proof
		var cachedHashes []Hash
		for b := 0; b <= 50; b++ {
			adds, duration, delHashes := sc.NextBlock(numAdds)

			// The blockProof is the proof for the utxos being
			// spent/deleted.
			blockProof, err := p.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzUndoProofChain fail at block %d. Error: %v", b, err)
			}

			// Sanity checking.
			err = p.Verify(delHashes, blockProof, false)
			if err != nil {
				t.Fatal(err)
			}

			// Sanity checking.
			for _, target := range blockProof.Targets {
				n, _, _, err := p.getNode(target)
				if err != nil {
					t.Fatalf("FuzzUndoProofChain fail at block %d. Error: %v", b, err)
				}
				if n == nil {
					t.Fatalf("FuzzUndoProofChain fail to read %d at block %d.", target, b)
				}
			}

			// For logging.
			origCachedHashes := make([]Hash, len(cachedHashes))
			copy(origCachedHashes, cachedHashes)

			// Cache new utxos that have a duration longer than 3.
			var remembers []uint32
			var newHashesToCache []Hash
			for i, add := range adds {
				if duration[i] > 3 {
					remembers = append(remembers, uint32(i))
					newHashesToCache = append(newHashesToCache, add.Hash)
				}
			}

			// expectedCachedHashes is the expected hashes after the
			// modify has happened.
			expectedCachedHashes := make([]Hash, len(cachedHashes))
			copy(expectedCachedHashes, cachedHashes)
			expectedCachedHashes = removeHashes(expectedCachedHashes, delHashes, func(elem Hash) Hash { return elem })
			expectedCachedHashes = append(expectedCachedHashes, newHashesToCache...)

			// Update the proof with the deletions and additions that
			// happen in this block.
			rootHashes := make([]Hash, len(p.Roots))
			for i := range rootHashes {
				rootHashes[i] = p.Roots[i].data
			}
			addHashes := make([]Hash, len(adds))
			for i := range addHashes {
				addHashes[i] = adds[i].Hash
			}

			prevRoots := make([]Hash, len(stump.Roots))
			copy(prevRoots, stump.Roots)

			updateData, err := stump.Update(delHashes, addHashes, blockProof)
			if err != nil {
				t.Fatal(err)
			}

			// Save the undo data to undo the cached proof.
			undoData = append(undoData,
				struct {
					addHashes  []Hash
					delHashes  []Hash
					targets    []uint64
					remembers  []uint32
					updateData UpdateData
					proof      Proof
					roots      []Hash

					blockHeight int
				}{
					addHashes,
					delHashes,
					blockProof.Targets,
					remembers,
					updateData,
					blockProof,
					prevRoots,

					b,
				},
			)

			cachedHashes, err = cachedProof.Update(cachedHashes, addHashes, blockProof.Targets, remembers, updateData)
			if err != nil {
				t.Fatal(err)
			}

			// Check that we have enough targets as we expect.
			if len(cachedProof.Targets) != len(cachedHashes) {
				t.Fatalf("FuzzUndoProofChain Fail. Expected %d "+
					"targets but got %d.\nDeleted hashes:\n%v"+
					"\nOriginal cached hashes:\n%v\nExpected "+
					"hashes:\n%v\nGot hashes:\n%v\n",
					len(cachedHashes),
					len(cachedProof.Targets),
					printHashes(delHashes),
					printHashes(origCachedHashes),
					printHashes(expectedCachedHashes),
					printHashes(cachedHashes))
			}

			shouldBeEmpty := make([]Hash, len(cachedHashes))
			copy(shouldBeEmpty, cachedHashes)

			// Check that all the hashes we expect to be cached are all there.
			shouldBeEmpty = removeHashes(shouldBeEmpty, cachedHashes, func(elem Hash) Hash { return elem })
			if len(shouldBeEmpty) > 0 {
				t.Fatalf("FuzzUndoProofChain Fail. Expected hashes:\n%s\nbut got:\n%s\n",
					printHashes(expectedCachedHashes), printHashes(cachedHashes))
			}
			err = p.Modify(adds, delHashes, blockProof)
			if err != nil {
				t.Fatalf("FuzzUndoProofChain fail at block %d. Error: %v", b, err)
			}

			// Sanity check that the modified proof verifies with the
			// modified pollard.
			err = p.Verify(cachedHashes, cachedProof, false)
			if err != nil {
				t.Fatalf("FuzzUndoProofChain fail at block %d. Error: %v", b, err)
			}

			_, err = Verify(stump, cachedHashes, cachedProof)
			if err != nil {
				t.Fatalf("FuzzUndoProofChain fail at block %d. Error: %v", b, err)
			}

			// Undo every 10 blocks. We only check the validity of the proof after
			// the undo. We don't check that all the relevant hashes are still cached.
			if b%3 == 2 {
				// Don't use the originals. Make a copy of the cachedHashes
				// and the cached proof.
				cachedHashesCopy := make([]Hash, len(cachedHashes))
				copy(cachedHashesCopy, cachedHashes)

				cachedProofCopy := Proof{make([]uint64, len(cachedProof.Targets)), make([]Hash, len(cachedProof.Proof))}
				copy(cachedProofCopy.Proof, cachedProof.Proof)
				copy(cachedProofCopy.Targets, cachedProof.Targets)

				// Undo the last 10 blocks.
				for i := 2; i >= 0; i-- {
					cachedHashesCopy, err = cachedProofCopy.Undo(
						uint64(len(undoData[i].addHashes)),
						undoData[i].updateData.PrevNumLeaves+uint64(len(undoData[i].addHashes)),
						undoData[i].targets,
						undoData[i].delHashes,
						cachedHashesCopy,
						undoData[i].updateData.ToDestroy,
						undoData[i].proof,
					)
					if err != nil {
						t.Fatalf("FuzzUndoProofChain error: %v", err)
					}

					_, err = Verify(
						Stump{
							undoData[i].roots,
							undoData[i].updateData.PrevNumLeaves,
						},
						undoData[i].delHashes,
						undoData[i].proof,
					)
					if err != nil {
						t.Fatalf("FuzzUndoProofChain error: %v", err)
					}
				}
				undoData = undoData[:0]
			}

			// Sanity checking.
			if b%10 == 0 {
				err = p.checkHashes()
				if err != nil {
					t.Fatal(err)
				}
			}

			err = p.posMapSanity()
			if err != nil {
				t.Fatalf("FuzzUndoProofChain fail at block %d. Error: %v",
					b, err)
			}
			if uint64(len(p.NodeMap)) != p.NumLeaves-p.NumDels {
				err := fmt.Errorf("FuzzUndoProofChain fail at block %d: "+
					"have %d leaves in map but only %d leaves in total",
					b, len(p.NodeMap), p.NumLeaves-p.NumDels)
				t.Fatal(err)
			}
		}
	})
}

func leafToHashes(leaves []Leaf) []Hash {
	hashes := make([]Hash, len(leaves))
	for i, leaf := range leaves {
		hashes[i] = leaf.Hash
	}

	return hashes
}

func FuzzUndoProof(f *testing.F) {
	var tests = []struct {
		seed        int64
		startLeaves uint8
		modifyAdds  uint8
		delCount    uint8
	}{
		{
			165465,
			8,
			2,
			3,
		},
		{
			-14465465,
			6,
			2,
			5,
		},
	}

	for _, test := range tests {
		f.Add(test.seed, test.startLeaves, test.modifyAdds, test.delCount)
	}

	f.Fuzz(func(t *testing.T, seed int64, startLeaves uint8, modifyAdds uint8, delCount uint8) {
		t.Parallel()

		rand.Seed(seed)
		// delCount must be less than the current number of leaves.
		if delCount > startLeaves {
			return
		}

		// Have at least 2 leaves left over.
		if startLeaves-delCount < 2 {
			return
		}

		// Create the starting off pollard.
		p := NewAccumulator()
		leaves, dels, _ := getAddsAndDels(uint32(p.NumLeaves), uint32(startLeaves), uint32(delCount))
		err := p.Modify(leaves, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}

		addHashes := leafToHashes(leaves)
		stump := Stump{}
		updateData, err := stump.Update(nil, addHashes, Proof{})
		if err != nil {
			t.Fatal(err)
		}

		indexes := randomIndexes(len(leaves), 1)
		remembers := make([]uint32, len(indexes))
		for i, index := range indexes {
			remembers[i] = uint32(index)
		}

		cachedProof := Proof{}
		cachedHashes, err := cachedProof.Update(nil, addHashes, nil, remembers, updateData)
		if err != nil {
			t.Fatal(err)
		}
		_, err = Verify(stump, cachedHashes, cachedProof)
		if err != nil {
			t.Fatal(err)
		}

		bp, err := p.Prove(dels)
		if err != nil {
			t.Fatal(err)
		}
		modifyLeaves, _, _ := getAddsAndDels(uint32(p.NumLeaves), uint32(modifyAdds), 0)
		err = p.Modify(modifyLeaves, dels, bp)
		if err != nil {
			t.Fatal(err)
		}

		prevStump := Stump{make([]Hash, len(stump.Roots)), stump.NumLeaves}
		copy(prevStump.Roots, stump.Roots)

		addHashes = leafToHashes(modifyLeaves)
		updateData, err = stump.Update(dels, addHashes, bp)
		if err != nil {
			t.Fatal(err)
		}

		indexes = randomIndexes(len(modifyLeaves), 1)
		remembers = make([]uint32, len(indexes))
		for i, index := range indexes {
			remembers[i] = uint32(index)
		}

		cachedHashes, err = cachedProof.Update(cachedHashes, addHashes, bp.Targets, remembers, updateData)
		if err != nil {
			t.Fatal(err)
		}

		_, err = Verify(stump, cachedHashes, cachedProof)
		if err != nil {
			t.Fatal(err)
		}

		cachedHashes, err = cachedProof.Undo(uint64(len(addHashes)), stump.NumLeaves, bp.Targets, dels, cachedHashes, updateData.ToDestroy, bp)
		if err != nil {
			t.Fatal(err)
		}
		_, err = Verify(prevStump, cachedHashes, cachedProof)
		if err != nil {
			t.Fatal(err)
		}
	})
}

func TestAddBlockSummary(t *testing.T) {
	tests := []struct {
		deletions [][]uint64
		numAdds   []uint16
	}{
		{
			deletions: [][]uint64{
				{},
				{},
			},
			numAdds: []uint16{
				3, 5,
			},
		},
		{
			deletions: [][]uint64{
				{},
				{1},
			},
			numAdds: []uint16{
				3, 5,
			},
		},
		{
			deletions: [][]uint64{
				{},
				{},
				{},
				{},
			},
			numAdds: []uint16{
				3, 5, 1, 0,
			},
		},
		{
			deletions: [][]uint64{
				{},
				{},
				{},
				{},
			},
			numAdds: []uint16{
				3, 5, 8, 0,
			},
		},
		{
			deletions: [][]uint64{
				{},
				{},
				{},
				{8},
			},
			numAdds: []uint16{
				3, 5, 1, 0,
			},
		},
	}

	for testIdx, test := range tests {
		cs := NewCachingScheduleTracker(0)

		for i, deletion := range test.deletions {
			add := test.numAdds[i]
			cs.AddBlockSummary(deletion, add)

			numLeaves := cs.numLeaves[len(cs.numLeaves)-1]
			expectedPos := RootPositions(numLeaves, TreeRows(numLeaves))

			height := int32(len(cs.numLeaves))
			gotPos := cs.getRoots(height)
			for j, expected := range expectedPos {
				if gotPos[j].pos != expected {
					t.Fatalf("%v, expected %v, got %v", testIdx, expectedPos, gotPos[j].pos)
				}
			}

			gotDeletions := cs.getDels(height)
			require.Equal(t, gotDeletions, deletion)
		}

		require.Equal(t, test.numAdds, cs.numAdds)
	}
}

func FuzzAddBlockSummary(f *testing.F) {
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

		p := NewAccumulator()
		stump := Stump{}
		cs := NewCachingScheduleTracker(50)

		for b := int32(1); b <= 50; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)

			// The blockProof is the proof for the utxos being
			// spent/deleted.
			blockProof, err := p.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzAddBlockSummary fail at block %d. Error: %v", b, err)
			}

			err = p.Modify(adds, delHashes, blockProof)
			if err != nil {
				t.Fatalf("FuzzAddBlockSummary fail at block %d. Error: %v", b, err)
			}

			addHashes := make([]Hash, 0, len(adds))
			for _, add := range adds {
				addHashes = append(addHashes, add.Hash)
			}
			updateData, err := stump.Update(delHashes, addHashes, blockProof)
			if err != nil {
				t.Fatalf("FuzzAddBlockSummary fail at block %d. Error: %v", b, err)
			}
			cs.AddBlockSummary(blockProof.Targets, uint16(len(adds)))

			gotToDestroy := cs.getToDestroy(b)
			require.Equal(t, updateData.ToDestroy, gotToDestroy)

			rootPositions := RootPositions(p.NumLeaves, TreeRows(p.NumLeaves))

			latestRoots := cs.getRoots(b)
			haveRoots := make([]uint64, 0, len(latestRoots))
			for _, rootPos := range latestRoots {
				haveRoots = append(haveRoots, rootPos.pos)
			}
			require.Equal(t, rootPositions, haveRoots)

			if len(latestRoots) != len(p.Roots) {
				t.Fatalf("expected %v roots but got %v",
					len(p.Roots), len(cs.roots))
			}
			for i, root := range latestRoots {
				isZombie := p.Roots[i].data == empty
				if isZombie != root.isZombie {
					t.Fatalf("expected %v for pos %v but got %v",
						isZombie, root.pos, root.isZombie)
				}
			}
		}
	})
}

func TestGetPrevPos(t *testing.T) {
	testCases := []struct {
		numLeaves       uint64
		deletions       []uint64
		toDestroy       []uint64
		numAdds         uint16
		cached          []uint64
		expectedCached  []uint64
		expectedCreated []uint64
	}{
		// 06:760d
		// |---------------\
		// 04:177a         05:0300
		// |-------\       |-------\
		// 00:0000 01:0100
		//
		// |---------------\
		// 04:177a
		// |-------\       |-------\
		// 00:0000 01:0100 02:XX
		{
			numLeaves:       4,
			deletions:       []uint64{},
			toDestroy:       []uint64{2},
			numAdds:         1,
			cached:          []uint64{translatePos(5, TreeRows(4), CSTTotalRows)},
			expectedCached:  []uint64{},
			expectedCreated: []uint64{3},
		},

		// 06:a3c3
		// |---------------\
		// 04:0200         05:0300
		// |-------\       |-------\
		//
		//
		// |---------------\
		// 04:XX
		// |-------\       |-------\
		//                 02:0200
		{
			numLeaves:       4,
			deletions:       []uint64{},
			toDestroy:       []uint64{translatePos(4, TreeRows(4), CSTTotalRows)},
			numAdds:         1,
			cached:          []uint64{translatePos(4, TreeRows(4), CSTTotalRows)},
			expectedCached:  []uint64{2},
			expectedCreated: []uint64{},
		},
	}

	for _, test := range testCases {
		gotCached, gotCreated, err := getPrevPos(CSTTotalRows, test.cached, test.deletions, test.toDestroy, test.numAdds, test.numLeaves)
		if err != nil {
			t.Fatal(err)
		}

		require.Equal(t, test.expectedCached, gotCached)
		require.Equal(t, test.expectedCreated, gotCreated)
	}
}

func FuzzGetPrevPos(f *testing.F) {
	var tests = []struct {
		numAdds  uint32
		duration uint32
		seed     int64
	}{
		{3, 3, 0xf1},
	}
	for _, test := range tests {
		f.Add(test.numAdds, test.duration, test.seed)
	}

	f.Fuzz(func(t *testing.T, numAdds, duration uint32, seed int64) {
		// simulate blocks with simchain
		sc := newSimChainWithSeed(duration, seed)

		cs := NewCachingScheduleTracker(10)

		addedPositions := make([][]uint64, 0, 10)

		p := NewAccumulator()
		stump := Stump{}
		for b := 0; b < 10; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)

			// The blockProof is the proof for the utxos being
			// spent/deleted.
			blockProof, err := p.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzGetPrevPos fail at block %d. Error: %v", b, err)
			}

			added := make([]uint64, 0, len(adds))
			for i := range adds {
				pos := p.GetNumLeaves() + uint64(i)
				added = append(added, pos)
			}
			addedPositions = append(addedPositions, added)

			err = p.Modify(adds, delHashes, blockProof)
			if err != nil {
				t.Fatalf("FuzzGetPrevPos fail at block %d. Error: %v", b, err)
			}
			addHashes := make([]Hash, 0, len(adds))
			for _, add := range adds {
				addHashes = append(addHashes, add.Hash)
			}
			_, err = stump.Update(delHashes, addHashes, blockProof)
			if err != nil {
				t.Fatalf("FuzzGetPrevPos fail at block %d. Error: %v", b, err)
			}

			cs.AddBlockSummary(blockProof.Targets, uint16(len(adds)))

			cached := make([]uint64, len(blockProof.Targets))
			copy(cached, translatePositions(blockProof.Targets, TreeRows(p.NumLeaves), CSTTotalRows))
			for i := b - 1; i >= 0; i-- {
				c, created, err := getPrevPos(CSTTotalRows, cached, cs.deletions[i],
					cs.toDestroy[i], cs.numAdds[i], cs.numLeaves[i])
				if err != nil {
					t.Fatalf("FuzzGetPrevPos fail at block %d. %v", b, err)
				}
				cached = c

				if i > 0 {
					cached = append(cached, cs.deletions[i]...)
				}
				created = translatePositions(created, CSTTotalRows, TreeRows(cs.numLeaves[i]))
				for _, pos := range created {
					idx := slices.Index(addedPositions[i], pos)
					if idx == -1 {
						t.Fatalf("FuzzGetPrevPos fail at block %d. "+
							"calculated created position %v at block %v"+
							" wasn't found",
							b, pos, i)
					}
				}
			}
		}
	})
}

func TestCachingSchedule(t *testing.T) {
	tests := []struct {
		name           string
		blockDeletions [][]uint64
		numAdds        []uint16
		maxMemory      int
		expected       [][]uint64
		expectErr      bool
	}{
		//{
		//	// creates(0, 1) | dels ()
		//	// creates(2, 3) | dels (0)
		//	// creates(4, 5) | dels (1)
		//	// creates(6, 7) | dels (2, 3)
		//	name: "Basic case",
		//	blockDeletions: [][]uint64{
		//		{},
		//		{0},
		//		{4},
		//		{8, 9},
		//	},
		//	numAdds:   []uint16{2, 2, 2, 2},
		//	maxMemory: 3,
		//	expected: [][]uint64{
		//		{0, 1},
		//		{2, 3},
		//		{},
		//		{},
		//	},
		//	expectErr: false,
		//},
		//{
		//	// creates(0, 1) | dels ()
		//	// creates(2, 3) | dels (0)
		//	// creates(4, 5) | dels (1)
		//	// creates(6, 7) | dels (2, 3)
		//	name: "Basic case with maxMemory of 2",
		//	blockDeletions: [][]uint64{
		//		{},
		//		{0},
		//		{4},
		//		{8, 9},
		//	},
		//	numAdds:   []uint16{2, 2, 2, 2},
		//	maxMemory: 2,
		//	expected: [][]uint64{
		//		{0, 1},
		//		{2},
		//		{},
		//		{},
		//	},
		//	expectErr: false,
		//},
		//{
		//	name: "No additions, no deletions",
		//	blockDeletions: [][]uint64{
		//		{},
		//		{},
		//		{},
		//		{},
		//	},
		//	numAdds:   []uint16{0, 0, 0, 0},
		//	maxMemory: 3,
		//	expected: [][]uint64{
		//		{}, {}, {}, {},
		//	},
		//	expectErr: false,
		//},
		//{
		//	// creates(0, 1, 2, 3, 4, 5, 6, 7) | dels ()
		//	// creates(8, 9, 10, 11, 12)       | dels ()
		//	// creates(13, 14, 15)             | dels ()
		//	name: "No deletions",
		//	blockDeletions: [][]uint64{
		//		{},
		//		{},
		//		{},
		//		{},
		//	},
		//	numAdds:   []uint16{8, 5, 3, 0},
		//	maxMemory: 3,
		//	expected: [][]uint64{
		//		{}, {}, {}, {},
		//	},
		//	expectErr: false,
		//},
		//{
		//	// creates(0, 1) | dels ()
		//	// creates(2, 3) | dels (0)
		//	// creates(4, 5) | dels (1, 2)
		//	// creates(6, 7) | dels (3, 4, 5)
		//	name: "Cache eviction when maxMemory is exceeded",
		//	blockDeletions: [][]uint64{
		//		{},
		//		{0},
		//		{4, 2},
		//		{12, 4, 5},
		//	},
		//	numAdds:   []uint16{2, 2, 2, 2},
		//	maxMemory: 2,
		//	expected: [][]uint64{
		//		{0, 1},
		//		{2},
		//		{4, 5},
		//		{},
		//	},
		//	expectErr: false,
		//},
		//{
		//	name: "Cache eviction with maxMemory at 1",
		//	blockDeletions: [][]uint64{
		//		{},
		//		{},
		//		{},
		//		{0, 1},
		//	},
		//	numAdds:   []uint16{7, 0, 0, 0},
		//	maxMemory: 1,
		//	expected: [][]uint64{
		//		{0},
		//		{},
		//		{},
		//		{},
		//	},
		//	expectErr: false,
		//},
		//{
		//	// creates(0, 1, 2, 3) | dels ()
		//	// creates(4, 5, 6, 7) | dels ()
		//	// creates()           | dels (0, 4)
		//	// creates()           | dels ()
		//	name: "Delete 2 leaves",
		//	blockDeletions: [][]uint64{
		//		{},
		//		{},
		//		{0, 4},
		//		{},
		//	},
		//	numAdds:   []uint16{4, 4, 0, 0},
		//	maxMemory: 1,
		//	expected: [][]uint64{
		//		{},
		//		{4},
		//		{},
		//		{},
		//	},
		//	expectErr: false,
		//},
		//{
		//	// creates(0, 1, 2, 3) | dels ()
		//	// creates(4, 5, 6, 7) | dels ()
		//	// creates()           | dels (0, 4, 5)
		//	// creates()           | dels ()
		//	name: "Delete 3 leaves",
		//	blockDeletions: [][]uint64{
		//		{},
		//		{},
		//		{0, 4, 5},
		//		{},
		//	},
		//	numAdds:   []uint16{4, 4, 0, 0},
		//	maxMemory: 2,
		//	expected: [][]uint64{
		//		{},
		//		{4, 5},
		//		{},
		//		{},
		//	},
		//	expectErr: false,
		//},
		//{
		//	// creates(0, 1, 2, 3) | dels ()
		//	// creates(4, 5, 6)    | dels ()
		//	// creates(7)          | dels ()
		//	// creates()           | dels (0, 4, 7)
		//	name: "Delete 3 leaves but created at different heights",
		//	blockDeletions: [][]uint64{
		//		{},
		//		{},
		//		{},
		//		{0, 4, 7},
		//	},
		//	numAdds:   []uint16{4, 3, 1, 0},
		//	maxMemory: 2,
		//	expected: [][]uint64{
		//		{},
		//		{4},
		//		{7},
		//		{},
		//	},
		//	expectErr: false,
		//},
		//{
		//	// creates(0, 1, 2, 3, 4, 5, 6) | dels ()
		//	// creates()                    | dels ()
		//	// creates()                    | dels ()
		//	// creates(7)                   | dels ()
		//	// creates()                    | dels (0, 4)
		//	// creates()                    | dels (7)
		//	name: "Expect to remove last deletion",
		//	blockDeletions: [][]uint64{
		//		{},
		//		{},
		//		{},
		//		{},
		//		{0, 4},
		//		{7},
		//	},
		//	numAdds:   []uint16{7, 0, 0, 1, 0, 0},
		//	maxMemory: 2,
		//	expected: [][]uint64{
		//		{0, 4}, {}, {}, {}, {}, {},
		//	},
		//	expectErr: false,
		//},
		//{
		//	// creates(0, 1, 2, 3, 4, 5) | dels ()
		//	// creates()                 | dels ()
		//	// creates()                 | dels ()
		//	// creates(6)                | dels ()
		//	// creates(7)                | dels (6)
		//	// creates()                 | dels (0, 7)
		//	name: "Case for when the cache is filled and un-filled. Expect to cache everything",
		//	blockDeletions: [][]uint64{
		//		{},
		//		{},
		//		{},
		//		{},
		//		{6},
		//		{0, 11},
		//	},
		//	numAdds:   []uint16{6, 0, 0, 1, 1, 0},
		//	maxMemory: 2,
		//	expected: [][]uint64{
		//		{0}, {}, {}, {6}, {7}, {},
		//	},
		//	expectErr: false,
		//},
		{
			// creates(0, 1, 2, 3, 4, 5) | dels ()
			// creates()                 | dels ()
			// creates()                 | dels ()
			// creates(6)                | dels ()
			// creates(7)                | dels (6)
			// creates()                 | dels (0, 5, 7)
			name: "Case for when the cache is filled and un-filled",
			blockDeletions: [][]uint64{
				{},
				{},
				{},
				{},
				{6},
				{0, 5, 11},
			},
			numAdds:   []uint16{6, 0, 0, 1, 1, 0},
			maxMemory: 2,
			expected: [][]uint64{
				{0}, {}, {}, {6}, {7}, {},
			},
			expectErr: false,
		},
		{
			// creates(0, 1, 2, 3, 4, 5) | dels ()
			// creates()                 | dels ()
			// creates(6)                | dels ()
			// creates()                 | dels ()
			// creates(7)                | dels (6)
			// creates()                 | dels (0, 5, 7)
			name: "Case for when the cache is filled and un-filled. 6 created earlier.",
			blockDeletions: [][]uint64{
				{},
				{},
				{},
				{},
				{6},
				{0, 5, 11},
			},
			numAdds:   []uint16{6, 0, 1, 0, 1, 0},
			maxMemory: 2,
			expected: [][]uint64{
				{0}, {}, {6}, {}, {7}, {},
			},
			expectErr: false,
		},
		{
			// creates(0, 1, 2, 3, 4, 5, 6, 7) | dels ()
			// creates()                       | dels ()
			// creates()                       | dels ()
			// creates()                       | dels (4)
			// creates()                       | dels (6)
			// creates()                       | dels (0, 5, 7)
			name: "Expect to choose deletions with lower ttl",
			blockDeletions: [][]uint64{
				{},
				{},
				{},
				{4},
				{6},
				{0, 10, 11},
			},
			numAdds:   []uint16{8, 0, 0, 0, 0, 0},
			maxMemory: 2,
			expected: [][]uint64{
				{4, 6}, {}, {}, {}, {}, {},
			},
			expectErr: false,
		},
		{
			// creates(0, 1, 2, 3, 4, 5) | dels ()
			// creates(6, 7)             | dels ()
			// creates()                 | dels ()
			// creates()                 | dels (4)
			// creates()                 | dels (5)
			// creates()                 | dels (0, 6, 7)
			name: "Expect to choose deletions with lower ttl. Cached deletions created at height 0",
			blockDeletions: [][]uint64{
				{},
				{},
				{},
				{4},
				{10},
				{0, 10, 11},
			},
			numAdds:   []uint16{8, 0, 0, 0, 0, 0},
			maxMemory: 2,
			expected: [][]uint64{
				{4, 5}, {}, {}, {}, {}, {},
			},
			expectErr: false,
		},
		{
			// creates(0)                   | dels ()
			// creates(1, 2, 3, 4, 5, 6, 7) | dels ()
			// creates()                    | dels (4)
			// creates()                    | dels (6)
			// creates()                    | dels (0, 5, 7)
			name: "Expect to choose deletions with lower ttl. Different create heights.",
			blockDeletions: [][]uint64{
				{},
				{},
				{},
				{4},
				{6},
				{0, 10, 11},
			},
			numAdds:   []uint16{1, 7, 0, 0, 0, 0},
			maxMemory: 2,
			expected: [][]uint64{
				{}, {4, 6}, {}, {}, {}, {},
			},
			expectErr: false,
		},
		{
			// creates(0)             | dels ()
			// creates(1, 2, 3, 4, 5) | dels ()
			// creates(6, 7)          | dels ()
			// creates()              | dels (6)
			// creates()              | dels (0, 1, 5, 7)
			name: "Expect to choose deletions with lower ttl. Force eviction.",
			blockDeletions: [][]uint64{
				{},
				{},
				{},
				{},
				{6},
				{0, 1, 5, 11},
			},
			numAdds:   []uint16{1, 5, 2, 0, 0, 0},
			maxMemory: 2,
			expected: [][]uint64{
				{}, {}, {6, 7}, {}, {}, {},
			},
			expectErr: false,
		},
		{
			// creates(0)             | dels ()
			// creates(1, 2, 3, 4, 5) | dels ()
			// creates(6, 7)          | dels ()
			// creates()              | dels (4)
			// creates()              | dels (6)
			// creates()              | dels (0, 5, 7)
			name: "Expect to choose deletions with lower ttl. Force eviction.",
			blockDeletions: [][]uint64{
				{},
				{},
				{},
				{4},
				{6},
				{0, 10, 11},
			},
			numAdds:   []uint16{1, 5, 2, 0, 0, 0},
			maxMemory: 2,
			expected: [][]uint64{
				{}, {}, {6, 7}, {}, {}, {},
			},
			expectErr: false,
		},
		{
			// creates(0, 1, 2, 3) | dels ()
			// creates()           | dels ()
			// creates()           | dels (0, 3)
			// creates(4, 5, 6)    | dels ()
			// creates()           | dels (4, 5, 6)
			// creates()           | dels (1, 2)
			name: "Cache emptied and filled",
			blockDeletions: [][]uint64{
				{},
				{},
				{0, 3},
				{},
				{4, 5, 6},
				{8, 9},
			},
			numAdds:   []uint16{4, 0, 0, 3, 0, 0},
			maxMemory: 2,
			expected: [][]uint64{
				{0, 3}, {}, {}, {4, 5}, {}, {},
			},
			expectErr: false,
		},
		{
			// creates(0, 1, 2, 3) | dels ()
			// creates()           | dels ()
			// creates()           | dels (0)
			// creates(4, 5, 6)    | dels ()
			// creates()           | dels (4, 5, 6)
			// creates()           | dels (1, 2)
			name: "Cache partially filled and then filled",
			blockDeletions: [][]uint64{
				{},
				{},
				{0},
				{},
				{4, 5, 6},
				{8, 2},
			},
			numAdds:   []uint16{4, 0, 0, 3, 0, 0},
			maxMemory: 2,
			expected: [][]uint64{
				{0}, {}, {}, {4, 5}, {}, {},
			},
			expectErr: false,
		},
		{
			// creates(0, 1, 2, 3) | dels ()
			// creates()           | dels ()
			// creates()           | dels (0, 3)
			// creates(4, 5, 6)    | dels ()
			// creates()           | dels (4, 5)
			// creates()           | dels (1)
			name: "Expect to cache everything",
			blockDeletions: [][]uint64{
				{},
				{},
				{0, 3},
				{},
				{4, 5},
				{8},
			},
			numAdds:   []uint16{4, 0, 0, 3, 0, 0},
			maxMemory: 3,
			expected: [][]uint64{
				{0, 1, 3}, {}, {}, {4, 5}, {}, {},
			},
			expectErr: false,
		},
		{
			// [2, 3, 5,       10,    12,         ]
			// [2, 3, 5, 7, 9, 10, 8, 12, 4, 6, 11]

			// creates(0, 1)   | dels ()
			// creates(2, 3)   | dels ()           | cache 2, 3
			// creates(4, 5)   | dels ()           | cache 5
			// creates(6, 7)   | dels ()
			// creates(8, 9)   | dels (2)
			// creates(10, 11) | dels (3, 5)       | cache 10
			// creates(12, 13) | dels (7, 9)       | cache 12
			// creates(14, 15) | dels (10)
			// creates(16, 17) | dels (8, 12)
			// creates(18, 19) | dels (4, 6, 11)

			// [2,    5, 7, 9, 10,    12,       11]
			// [2, 3, 5, 7, 9, 10, 8, 12, 4, 6, 11]

			// creates (0, 1)   | ()
			// creates (2, 3)   | ()                                 | cache 2
			// creates (4, 5)   | (2)                                | cache 5
			// creates (6, 7)   | (5, 3) (2)                         | cache 7
			// creates (8, 9)   | (7, 5, 3) (2)                      | cache 9
			// creates (10, 11) | (9, 7, 5, 3)                       | cache 10, 11
			// creates (12, 13) | (11, 6, 4, 8, 10) (9, 7)           | cache 12
			// creates (14, 15) | (11, 6, 4, 12, 8, 10)
			// creates (16, 17) | (11, 6, 4, 12, 8)
			// creates (18, 19) | (11, 6, 4)

			// [2, 3, 5,    9, 10,    12,       11]
			// [2, 3, 5, 7, 9, 10, 8, 12, 4, 6, 11]

			// creates(0, 1)   | cache()           | ttl()        | dels ()
			// creates(2, 3)   | cache(2, 3)       | ttl(3, 4)    | dels ()
			// creates(4, 5)   | cache(2, 3, 5)    | ttl(2, 3, 3) | dels ()
			// creates(6, 7)   | cache(2, 3, 5)    | ttl(1, 2, 2) | dels ()
			// creates(8, 9)   | cache(3, 5, 9)    | ttl(1, 1, 2) | dels (2)
			// creates(10, 11) | cache(9, 10, 11)  | ttl(1, 2, 4) | dels (3, 5)
			// creates(12, 13) | cache(10, 11, 12) | ttl(1, 3, 2) | dels (7, 9)
			// creates(14, 15) | cache(11, 12)     | ttl(2, 1)    | dels (10)
			// creates(16, 17) | cache(11)         | ttl(1)       | dels (8, 12)
			// creates(18, 19) | cache()           | ttl()        | dels (4, 6, 11)
			name: "Fuzz failure case 1",
			blockDeletions: [][]uint64{
				{},
				{},
				{},
				{},
				{2},
				{17, 5},
				{7, 9},
				{10},
				{20, 12},
				{34, 35, 50},
			},
			numAdds:   []uint16{2, 2, 2, 2, 2, 2, 2, 2, 2, 2},
			maxMemory: 3,
			expected: [][]uint64{
				{}, {2}, {5}, {7}, {9}, {10, 11}, {12}, {}, {}, {},
			},
			expectErr: false,
		},
	}

	for _, tt := range tests {
		cs := NewCachingScheduleTracker(0)
		for i, numAdd := range tt.numAdds {
			cs.AddBlockSummary(tt.blockDeletions[i], numAdd)
		}

		result, err := cs.GenerateCachingSchedule(tt.maxMemory)
		for i, row := range result {
			numLeaves := uint64(0)
			if i != 0 {
				numLeaves = cs.numLeaves[i-1]
			}
			for j := range row {
				row[j] += numLeaves
			}
		}

		if tt.expectErr {
			if err == nil {
				t.Errorf("Test %s: expected an error but got nil", tt.name)
			}
		} else {
			if err != nil {
				t.Errorf("Test %s: unexpected error: %v", tt.name, err)
			}

			require.Equal(t, tt.expected, result)
		}
	}
}

func FuzzGenerateCachingSchedule(f *testing.F) {
	var tests = []struct {
		numAdds  uint32
		duration uint32
		seed     int64
	}{
		{2, 0x07, 0x07},
	}
	for _, test := range tests {
		f.Add(test.numAdds, test.duration, test.seed)
	}

	f.Fuzz(func(t *testing.T, numAdds, duration uint32, seed int64) {
		t.Parallel()

		// simulate blocks with simchain
		sc := newSimChainWithSeed(duration, seed)

		//blockNum := 1000
		blockNum := 10
		dels := make([][]Hash, 0, blockNum)
		adds := make([][]Leaf, 0, blockNum)
		durations := make([][]int32, 0, blockNum)

		cs := NewCachingScheduleTracker(blockNum)

		p := NewAccumulator()
		for b := 1; b <= blockNum; b++ {
			add, duration, delHashes := sc.NextBlock(numAdds)

			adds = append(adds, add)
			durations = append(durations, duration)
			dels = append(dels, delHashes)

			proof, err := p.Prove(delHashes)
			if err != nil {
				t.Fatal(err)
			}

			fmt.Printf("%v deleted %v\n%v\n", b, proof.Targets, printHashes(delHashes))
			err = p.Modify(add, delHashes, proof)
			if err != nil {
				t.Fatal(err)
			}

			fmt.Println(p.String())

			cs.AddBlockSummary(proof.Targets, uint16(len(add)))
		}

		maxMem := 3
		cachingSchedule, err := cs.GenerateCachingSchedule(maxMem)
		if err != nil {
			t.Fatal(err)
		}

		fmt.Println("cachingSchedule", cachingSchedule)

		err = verifyCachingIsOptimal(maxMem, durations, cachingSchedule, dels, adds)
		if err != nil {
			t.Fatal(err)
		}
	})
}

// If index i is not cached, nothing coming after it should be cached.
func checkNextIndexesAreUncached(cacheSchedule []uint64, adds []Leaf) error {
	if len(cacheSchedule) > len(adds) {
		return fmt.Errorf("have more cacheSchedules with %v, than adds with a count of %v",
			len(cacheSchedule), len(adds))
	}

	for i, pos := range cacheSchedule {
		if i+1 < len(cacheSchedule) {
			if pos > cacheSchedule[i+1] {
				return fmt.Errorf("cache schedule not in order")
			}

			if pos == cacheSchedule[i+1] {
				return fmt.Errorf("cache schedule hash duplicates")
			}
		}
	}

	return nil
}

func verifyCachingIsOptimal(maxMem int, durations [][]int32, cacheSchedules [][]uint64, dels [][]Hash, adds [][]Leaf) error {
	uncached := make(map[Hash][2]int32)
	currentCached := make(map[Hash]int32)

	for i, cacheSchedule := range cacheSchedules {
		fmt.Println(cacheSchedule)
		// Remove from maps.
		for _, del := range dels[i] {
			//fmt.Println("remove", i, del)
			delete(currentCached, del)
			delete(uncached, del)
		}

		err := checkNextIndexesAreUncached(cacheSchedule, adds[i])
		if err != nil {
			return err
		}

		cacheIdx := 0
		for j, add := range adds[i] {
			// Calculate spent height.
			duration := durations[i][j]
			spentHeight := duration
			if duration != 0 {
				spentHeight = duration + int32(i)
			}

			// Check if the added leaf is supposed to be cached.
			isCached := false
			if cacheIdx < len(cacheSchedule) && j == int(cacheSchedule[cacheIdx]) {
				isCached = true
				//fmt.Println("cache", add, cacheSchedule[cacheIdx])
				cacheIdx++
			} else {
				//fmt.Println("not cache")
			}

			if isCached {
				currentCached[add.Hash] = spentHeight
				if duration == 0 {
					return fmt.Errorf("have cached %v but it is not spent", add.Hash)
				}

				// Make sure all the uncached leaves are not spent before this leaf.
				for uncachedHash, uncachedSpentHeight := range uncached {
					if uncachedSpentHeight[0] == 0 {
						continue
					}

					if spentHeight > uncachedSpentHeight[1] {
						fmt.Printf("uncached dur %v, mydur %v\n", uncachedSpentHeight[0]-int32(i), duration)
						return fmt.Errorf("cached %v spent at %v but earlier %v spent at %v",
							add.Hash, spentHeight, uncachedHash, uncachedSpentHeight)
					}
				}
			} else {
				spentHeight := duration
				if duration != 0 {
					spentHeight = duration + int32(i)
				}
				uncached[add.Hash] = [2]int32{duration, spentHeight}
			}
		}

		// Make sure we don't go over the maxmem limit.
		if len(currentCached) > maxMem {
			fmt.Println("cached\n", currentCached)
			fmt.Println(i)
			return fmt.Errorf("have %v cached but maxmem is %v", len(currentCached), maxMem)
		}

		// Because our cache is full, we don't penalize for omitting these from the cache
		// instead of later leaves. If we're optimal here, that's the best we can do and
		// we can't cache these in the future.
		if len(currentCached) == maxMem {
			uncached = make(map[Hash][2]int32)
		}
	}

	return nil
}
