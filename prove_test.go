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
	proofPos, _ := proofPositions(proof.Targets, p.NumLeaves, treeRows(p.NumLeaves))
	currentHashes := toHashAndPos(proofPos, proof.Proof)
	// Append the needed hashes to the proof.
	currentHashes.AppendMany(neededHashes.positions, neededHashes.hashes)

	// As new targets are added, we're able to calulate positions that we couldn't before. These positions
	// may already exist as proofs. Remove these as duplicates are not expected during proof verification.
	_, calculateables := proofPositions(desiredPositions, p.NumLeaves, treeRows(p.NumLeaves))
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
		rand.Seed(seed)

		// It'll error out if we try to delete more than we have. >= since we want
		// at least 2 leftOver leaf to test.
		if int(delCount) >= int(startLeaves)-2 {
			return
		}

		// Create the starting off pollard.
		p := NewAccumulator(true)
		leaves, delHashes, delPos := getAddsAndDels(uint32(p.NumLeaves), startLeaves, delCount)
		err := p.Modify(leaves, nil, nil)
		if err != nil {
			t.Fatal(err)
		}
		err = p.Modify(nil, delHashes, delPos)
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
		err = p.Verify(newDelHashes, newProof)
		if err != nil {
			t.Fatalf("FuzzGetMissingPositions fail: New proof failed to verify. error: %v", err)
		}
	})
}

func FuzzRemoveTargets(f *testing.F) {
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
		rand.Seed(seed)

		// It'll error out if we try to delete more than we have. >= since we want
		// at least 2 leftOver leaf to test.
		if int(delCount) >= int(startLeaves)-2 {
			return
		}

		// Get leaves and dels.
		leaves, delHashes, delPos := getAddsAndDels(0, startLeaves, delCount)

		// Create the starting off pollard.
		p := NewAccumulator(true)
		err := p.Modify(leaves, nil, nil)
		if err != nil {
			t.Fatal(err)
		}
		err = p.Modify(nil, delHashes, delPos)
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
		indexes := randomIndexes(currentLeaves.Len(), 2)
		leafSubset := hashAndPos{make([]uint64, 0, len(indexes)), make([]Hash, 0, len(indexes))}
		for i := 0; i < len(indexes); i++ {
			leafSubset.Append(currentLeaves.positions[indexes[i]],
				currentLeaves.hashes[indexes[i]])
		}

		// Generate a proof of the leafSubset.
		proof, err := p.Prove(leafSubset.hashes)
		if err != nil {
			t.Fatal(err)
		}

		// Randomly generate some positions to delete.
		indexes = randomIndexes(leafSubset.Len(), 1)
		positions := make([]uint64, len(indexes))
		for i := range positions {
			positions[i] = leafSubset.positions[indexes[i]]
		}

		// Delete the targets from the proof and verify the modified proof.
		newDelHashes, newproof := RemoveTargets(p.NumLeaves, leafSubset.hashes, proof, positions)

		err = p.Verify(newDelHashes, newproof)
		if err != nil {
			t.Fatalf("FuzzRemoveTargets fail. Error: %v\n\nWas removing targets:\n%v\n"+
				"from proof:\n%s\nGot proof:\n%s\nPollard:\n%s", err,
				positions, proof.String(), newproof.String(), p.String())
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
		rand.Seed(seed)

		// It'll error out if we try to delete more than we have. >= since we want
		// at least 2 leftOver leaf to test.
		if int(delCount) >= int(startLeaves)-2 {
			return
		}

		// Get leaves and dels.
		leaves, delHashes, delPos := getAddsAndDels(0, startLeaves, delCount)

		// Create the starting off pollard.
		p := NewAccumulator(true)
		err := p.Modify(leaves, nil, nil)
		if err != nil {
			t.Fatal(err)
		}
		err = p.Modify(nil, delHashes, delPos)
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
		sortedProofATargets := copySortedFunc(proofA.Targets, uint64Less)
		sortedProofBTargets := copySortedFunc(proofB.Targets, uint64Less)
		expectedTargets := mergeSortedSlicesFunc(sortedProofATargets, sortedProofBTargets, uint64Cmp)

		// This is the targets that we got from AddProof.
		sortedProofCTargets := copySortedFunc(proofC.Targets, uint64Less)

		// When we subtract the slice, we should get nothing since sortedProofCTargets and expectedTargets should
		// be the same.
		shouldBeEmpty := subtractSortedSlice(sortedProofCTargets, expectedTargets, uint64Cmp)
		if len(shouldBeEmpty) > 0 {
			t.Fatalf("FuzzAddProof Fail. Not all wanted targets were added. Expected %v, got %v",
				expectedTargets, proofC.Targets)
		}

		// Check that the proof verifies.
		err = p.Verify(leafHashesC, proofC)
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
		rand.Seed(seed)

		// It'll error out if we try to delete more than we have. >= since we want
		// at least 2 leftOver leaf to test.
		if int(delCount) >= int(startLeaves)-2 {
			return
		}

		// Get leaves and dels.
		leaves, delHashes, delPos := getAddsAndDels(0, startLeaves, delCount)

		// Create the starting off pollard.
		p := NewAccumulator(true)
		err := p.Modify(leaves, nil, nil)
		if err != nil {
			t.Fatal(err)
		}
		err = p.Modify(nil, delHashes, delPos)
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
		updated, _ := calculateHashes(p.NumLeaves, nil, blockProof)
		leafSubset.hashes = cachedProof.updateProofRemove(blockProof.Targets, leafSubset.hashes, updated, p.NumLeaves)

		// Modify the pollard.
		err = p.Modify(nil, blockDelHashes, delPositions)
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

		cachedProofPos, _ := proofPositions(cachedProof.Targets, p.NumLeaves, treeRows(p.NumLeaves))
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
		err = p.Verify(leafSubset.hashes, cachedProof)
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
		rand.Seed(seed)

		// It'll error out if we try to delete more than we have. >= since we want
		// at least 2 leftOver leaf to test.
		if int(delCount) >= int(startLeaves)-2 {
			return
		}

		// Get leaves and dels.
		leaves, delHashes, delPos := getAddsAndDels(0, startLeaves, delCount)

		// Create the starting off pollard.
		p := NewAccumulator(true)
		err := p.Modify(leaves, nil, nil)
		if err != nil {
			t.Fatal(err)
		}
		err = p.Modify(nil, delHashes, delPos)
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
		err = p.Modify(addLeaves, nil, nil)
		if err != nil {
			t.Fatal(err)
		}
		afterPollardStr := p.String()

		// And verify that the proof is correct.
		err = p.Verify(leafSubset.hashes, cachedProof)
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
		// simulate blocks with simchain
		sc := newSimChainWithSeed(duration, seed)

		p := NewAccumulator(true)
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
			err = p.Verify(delHashes, blockProof)
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

			err = p.Modify(adds, delHashes, blockProof.Targets)
			if err != nil {
				t.Fatalf("FuzzModifyProof fail at block %d. Error: %v", b, err)
			}

			p.Undo(uint64(len(adds)), blockProof.Targets, delHashes, stump.Roots)

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
			err = p.Modify(adds, delHashes, blockProof.Targets)
			if err != nil {
				t.Fatalf("FuzzModifyProof fail at block %d. Error: %v", b, err)
			}

			// Sanity check that the modified proof verifies with the
			// modified pollard.
			err = p.Verify(cachedHashes, cachedProof)
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
		rand.Seed(seed)

		// It'll error out if we try to delete more than we have. >= since we want
		// at least 3 leftOver leaf to test.
		if int(delCount) >= int(startLeaves)-3 {
			return
		}

		// Get leaves and dels.
		leaves, delHashes, delPos := getAddsAndDels(0, startLeaves, delCount)

		// Create the starting off pollard.
		p := NewAccumulator(true)
		err := p.Modify(leaves, nil, nil)
		if err != nil {
			t.Fatal(err)
		}
		err = p.Modify(nil, delHashes, delPos)
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
		err = p.Verify(leafSubset.hashes, cachedProof)
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
		expectedEmpty := copySortedFunc(provePositions, uint64Less)
		expectedEmpty = subtractSortedSlice(expectedEmpty, subsetProof.Targets, uint64Cmp)
		if len(expectedEmpty) > 0 {
			t.Fatalf("Positions %v did not get proven. All wanted positions: %v",
				expectedEmpty, provePositions)
		}

		// Verify the proof.
		err = p.Verify(subsetHashes, subsetProof)
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
