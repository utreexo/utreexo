package utreexo

import (
	"fmt"
	"math/rand"
	"reflect"
	"sort"
	"testing"

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
