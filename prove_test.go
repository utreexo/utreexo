package utreexo

import (
	"fmt"
	"math/rand"
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
	leftOutLeaves, leaves []hashAndPos) (Proof, []Hash, error) {

	// Grab all the hashes that are needed from the pollard.
	neededHashes := []hashAndPos{}
	sort.Slice(missingPositions, func(a, b int) bool { return missingPositions[a] < missingPositions[b] })
	for _, pos := range missingPositions {
		hash := p.getHash(pos)
		if hash == empty {
			return Proof{}, nil, fmt.Errorf("Couldn't fetch required hash at position %d", pos)
		}

		neededHashes = append(neededHashes, hashAndPos{hash, pos})
	}

	// Attach positions to the proof hashes.
	proofPos, _ := proofPositions(proof.Targets, p.NumLeaves, treeRows(p.NumLeaves))
	currentHashes := toHashAndPos(proofPos, proof.Proof)
	// Append the needed hashes to the proof.
	currentHashes = append(currentHashes, neededHashes...)

	// As new targets are added, we're able to calulate positions that we couldn't before. These positions
	// may already exist as proofs. Remove these as duplicates are not expected during proof verification.
	_, calculateables := proofPositions(desiredPositions, p.NumLeaves, treeRows(p.NumLeaves))
	for _, cal := range calculateables {
		idx := slices.IndexFunc(currentHashes, func(hnp hashAndPos) bool { return hnp.pos == cal })
		if idx != -1 {
			currentHashes = append(currentHashes[:idx], currentHashes[idx+1:]...)
		}
	}

	// The newly added targets may be used as proofs. Remove existing duplicates from the proof as these
	// are not expected during proof verification.
	for _, leaf := range leftOutLeaves {
		idx := slices.IndexFunc(currentHashes, func(hnp hashAndPos) bool { return hnp.hash == leaf.hash })
		if idx != -1 {
			currentHashes = append(currentHashes[:idx], currentHashes[idx+1:]...)
		}
	}

	// Create the proof.
	newProof := Proof{Targets: append(proof.Targets, desiredPositions...)}
	// Sort the targets as it needs to match the ordering of the deletion hashes and
	// the deletions hashes will also be sorted.
	sort.Slice(newProof.Targets, func(a, b int) bool { return newProof.Targets[a] < newProof.Targets[b] })

	// We need to sort the proof hashes as those are expected to be in order during proof verificatin.
	sort.Slice(currentHashes, func(a, b int) bool { return currentHashes[a].pos < currentHashes[b].pos })
	newProof.Proof = make([]Hash, len(currentHashes))
	for i := range newProof.Proof {
		newProof.Proof[i] = currentHashes[i].hash
	}

	// The deletion hashes are leaves + leftOutLeaves. We sort them to match the ordering of the targets.
	leaves = append(leaves, leftOutLeaves...)
	sort.Slice(leaves, func(a, b int) bool { return leaves[a].pos < leaves[b].pos })
	newDelHashes := make([]Hash, len(leaves))
	for i := range leaves {
		newDelHashes[i] = leaves[i].hash
	}

	return newProof, newDelHashes, nil
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
		currentLeaves := make([]hashAndPos, 0, len(leaves)-len(delHashes))
		for _, node := range p.NodeMap {
			currentLeaves = append(currentLeaves,
				hashAndPos{node.data, p.calculatePosition(node)})
		}
		// Sort to have a deterministic order of the currentLeaves. Since maps aren't
		// guaranteed to have the same order, we need to do this.
		sort.Slice(currentLeaves, func(a, b int) bool { return currentLeaves[a].pos < currentLeaves[b].pos })

		// Sanity check.
		if len(currentLeaves) != len(leaves)-len(delHashes) {
			t.Fatalf("FuzzGetMissingPositions fail. Expected %d leaves but have %d in the pollard map",
				len(leaves)-len(delHashes), len(currentLeaves))
		}

		// Randomly grab some leaves.
		indexes := randomIndexes(len(currentLeaves), 2)
		leafSubset := make([]hashAndPos, len(indexes))
		for i := range leafSubset {
			leafSubset[i] = currentLeaves[indexes[i]]
		}

		// Grab at least 1 leaf to leave out.
		leaveOutCount := rand.Intn(len(leafSubset)-1) + 1
		for leaveOutCount <= len(leafSubset)-1 && leaveOutCount < 1 {
			leaveOutCount++
		}
		// Randomly select leaves to leave out.
		leftOutLeaves := make([]hashAndPos, leaveOutCount)
		for i := range leftOutLeaves {
			// Randomly select a leaf to leave out.
			hashIdx := rand.Intn(len(leafSubset) - 1)
			leftOutLeaves[i] = leafSubset[hashIdx]

			// Remove the selected leaf from the subset.
			leafSubset = append(leafSubset[:hashIdx], leafSubset[hashIdx+1:]...)
		}
		hashes := make([]Hash, len(leafSubset))
		for i := range hashes {
			hashes[i] = leafSubset[i].hash
		}

		// Grab the proof of the leaves that we didn't leave out.
		proof, err := p.Prove(hashes)
		if err != nil {
			t.Fatal(err)
		}

		// Grab the positions of the leaves that we left out.
		desiredPositions := make([]uint64, len(leftOutLeaves))
		for i := range desiredPositions {
			desiredPositions[i] = leftOutLeaves[i].pos
		}

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
		currentLeaves := make([]hashAndPos, 0, len(leaves)-len(delHashes))
		for _, node := range p.NodeMap {
			currentLeaves = append(currentLeaves,
				hashAndPos{node.data, p.calculatePosition(node)})
		}
		// Sort to have a deterministic order of the currentLeaves. Since maps aren't
		// guaranteed to have the same order, we need to do this.
		sort.Slice(currentLeaves, func(a, b int) bool { return currentLeaves[a].pos < currentLeaves[b].pos })

		// Randomly grab some leaves.
		indexes := randomIndexes(len(currentLeaves), 2)
		leafSubset := make([]hashAndPos, len(indexes))
		for i := range leafSubset {
			leafSubset[i] = currentLeaves[indexes[i]]
		}

		// Generate a proof of the leafSubset.
		leafHashes := make([]Hash, len(leafSubset))
		for i := range leafHashes {
			leafHashes[i] = leafSubset[i].hash
		}
		proof, err := p.Prove(leafHashes)
		if err != nil {
			t.Fatal(err)
		}

		// Randomly generate some positions to delete.
		leafPositions := make([]uint64, len(leafSubset))
		for i := range leafPositions {
			leafPositions[i] = leafSubset[i].pos
		}
		indexes = randomIndexes(len(leafPositions), 1)
		positions := make([]uint64, len(indexes))
		for i := range positions {
			positions[i] = leafPositions[indexes[i]]
		}

		// Delete the targets from the proof and verify the modified proof.
		newDelHashes, newproof := RemoveTargets(p.NumLeaves, leafHashes, proof, positions)

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
		currentLeaves := make([]hashAndPos, 0, len(leaves)-len(delHashes))
		for _, node := range p.NodeMap {
			currentLeaves = append(currentLeaves,
				hashAndPos{node.data, p.calculatePosition(node)})
		}
		// Sort to have a deterministic order of the currentLeaves. Since maps aren't
		// guaranteed to have the same order, we need to do this.
		sort.Slice(currentLeaves, func(a, b int) bool { return currentLeaves[a].pos < currentLeaves[b].pos })

		// Randomly grab some leaves.
		indexesA := randomIndexes(len(currentLeaves), 2)
		leafSubsetA := make([]hashAndPos, len(indexesA))
		for i := range leafSubsetA {
			leafSubsetA[i] = currentLeaves[indexesA[i]]
		}

		indexesB := randomIndexes(len(currentLeaves), 2)
		leafSubsetB := make([]hashAndPos, len(indexesB))
		for i := range leafSubsetB {
			leafSubsetB[i] = currentLeaves[indexesB[i]]
		}

		// Generate a proof of the leafSubset.
		leafHashesA := make([]Hash, len(leafSubsetA))
		for i := range leafHashesA {
			leafHashesA[i] = leafSubsetA[i].hash
		}
		proofA, err := p.Prove(leafHashesA)
		if err != nil {
			t.Fatal(err)
		}

		leafHashesB := make([]Hash, len(leafSubsetB))
		for i := range leafHashesB {
			leafHashesB[i] = leafSubsetB[i].hash
		}
		proofB, err := p.Prove(leafHashesB)
		if err != nil {
			t.Fatal(err)
		}

		// Add the proof.
		leafHashesC, proofC := AddProof(proofA, proofB, leafHashesA, leafHashesB, p.NumLeaves)

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

func FuzzProofAfterDeletion(f *testing.F) {
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
		currentLeaves := make([]hashAndPos, 0, len(leaves)-len(delHashes))
		for _, node := range p.NodeMap {
			currentLeaves = append(currentLeaves,
				hashAndPos{node.data, p.calculatePosition(node)})
		}
		// Sort to have a deterministic order of the currentLeaves. Since maps aren't
		// guaranteed to have the same order, we need to do this.
		sort.Slice(currentLeaves, func(a, b int) bool { return currentLeaves[a].pos < currentLeaves[b].pos })

		// Randomly grab some leaves.
		indexes := randomIndexes(len(currentLeaves), 2)
		leafSubset := make([]hashAndPos, len(indexes))
		for i := range leafSubset {
			leafSubset[i] = currentLeaves[indexes[i]]
		}
		// Generate a proof of the leafSubset.
		leafHashes := make([]Hash, len(leafSubset))
		for i := range leafHashes {
			leafHashes[i] = leafSubset[i].hash
		}
		proof, err := p.Prove(leafHashes)
		if err != nil {
			t.Fatal(err)
		}

		// Randomly generate some positions to delete.
		leafPositions := make([]uint64, len(leafSubset))
		for i := range leafPositions {
			leafPositions[i] = leafSubset[i].pos
		}
		indexes = randomIndexes(len(leafPositions), 1)
		positions := make([]uint64, len(indexes))
		for i := range positions {
			positions[i] = leafPositions[indexes[i]]
		}

		// Delete the positions from the cached proof.
		leafHashes, proof = proofAfterPartialDeletion(p.NumLeaves, proof, leafHashes, positions)

		proofPos, _ := proofPositions(proof.Targets, p.NumLeaves, treeRows(p.NumLeaves))
		if len(proofPos) != len(proof.Proof) {
			t.Fatalf("FuzzProofAfterDeletion Fail. Have %v proofs but want %v.\nPollard:\n%s\n",
				printHashes(proof.Proof), proofPos, p.String())
		}

		// Fetch hashes.
		blockDelHashes := make([]Hash, len(positions))
		for i := range blockDelHashes {
			blockDelHashes[i] = p.getHash(positions[i])
			if blockDelHashes[i] == empty {
				t.Fatal("FuzzProofAfterDeletion Fail. Couldn't fetch hash for position", positions[i])
			}
		}

		// Modify the pollard.
		err = p.Modify(nil, blockDelHashes, positions)
		if err != nil {
			t.Fatal(err)
		}

		// And verify that the proof is correct.
		err = p.Verify(leafHashes, proof)
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
		currentLeaves := make([]hashAndPos, 0, len(leaves)-len(delHashes))
		for _, node := range p.NodeMap {
			currentLeaves = append(currentLeaves,
				hashAndPos{node.data, p.calculatePosition(node)})
		}
		// Sort to have a deterministic order of the currentLeaves. Since maps aren't
		// guaranteed to have the same order, we need to do this.
		sort.Slice(currentLeaves, func(a, b int) bool { return currentLeaves[a].pos < currentLeaves[b].pos })

		// Randomly grab some leaves.
		indexes := randomIndexes(len(currentLeaves), 2)
		leafSubset := make([]hashAndPos, len(indexes))
		for i := range leafSubset {
			leafSubset[i] = currentLeaves[indexes[i]]
		}
		// Generate a proof of the leafSubset.
		leafHashes := make([]Hash, len(leafSubset))
		for i := range leafHashes {
			leafHashes[i] = leafSubset[i].hash
		}
		cachedProof, err := p.Prove(leafHashes)
		if err != nil {
			t.Fatal(err)
		}

		// Randomly generate some positions to delete.
		delIndexes := randomIndexes(len(currentLeaves), 1)
		delLeaves := make([]hashAndPos, len(delIndexes))
		for i := range delLeaves {
			delLeaves[i] = currentLeaves[delIndexes[i]]
		}

		delPositions := make([]uint64, len(delLeaves))
		for i := range delPositions {
			delPositions[i] = delLeaves[i].pos
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
		origTargetsAndHash := toHashAndPos(cachedProof.Targets, leafHashes)

		// Delete the block hashes from the cached hashes. We'll use this to make
		// sure that the proof proves what we want to prove.
		cachedTargetsAndHash := toHashAndPos(cachedProof.Targets, leafHashes)
		blockDelTargetsAndHash := toHashAndPos(blockProof.Targets, blockDelHashes)
		cachedTargetsAndHash = subtractSortedSlice(cachedTargetsAndHash, blockDelTargetsAndHash, hashAndPosCmp)

		// Update the cached proof with the block proof.
		leafHashes, cachedProof = UpdateProofRemove(cachedProof, blockProof, leafHashes, blockDelHashes, p.NumLeaves)

		// Modify the pollard.
		err = p.Modify(nil, blockDelHashes, delPositions)
		if err != nil {
			t.Fatal(err)
		}

		// Check that we have enough targets as we expect.
		if len(cachedProof.Targets) != len(cachedTargetsAndHash) {
			t.Fatalf("FuzzUpdateProofRemove Fail. Expected %d targets but got %d."+
				"\nDeleted targets:\n%v.\nOriginal cached targets:\n%v\nExpected old targets:\n%v\n"+
				"Got targets:\n%v\nPollard before:\n%s\nPollard after:\n%s\n",
				len(cachedTargetsAndHash), len(cachedProof.Targets), blockProof.Targets,
				hashAndPosToString(origTargetsAndHash), hashAndPosToString(cachedTargetsAndHash),
				cachedProof.Targets, pollardBeforeStr, p.String())
		}

		shouldBeEmpty := make([]hashAndPos, len(cachedTargetsAndHash))
		copy(shouldBeEmpty, cachedTargetsAndHash)
		leafHashesAndPos := toHashAndPos(cachedProof.Targets, leafHashes)

		// Check that all the hashes we expect to be cached are all there.
		shouldBeEmpty = removeHashes(shouldBeEmpty, leafHashesAndPos, func(elem hashAndPos) Hash { return elem.hash })
		if len(shouldBeEmpty) > 0 {
			expectedHashes := make([]Hash, len(cachedTargetsAndHash))
			for i, cachedTargetAndHash := range cachedTargetsAndHash {
				expectedHashes[i] = cachedTargetAndHash.hash
			}

			t.Fatalf("FuzzUpdateProofRemove Fail. Expected hashes:\n%s\nbut got:\n%s\n",
				printHashes(expectedHashes), printHashes(leafHashes))
		}

		cachedProofPos, _ := proofPositions(cachedProof.Targets, p.NumLeaves, treeRows(p.NumLeaves))
		if len(cachedProofPos) != len(cachedProof.Proof) {
			t.Fatalf("FuzzUpdateProofRemove Fail. CachedProof hashes:\n%v\nbut want these positions:\n%v.\nPollard:\n%s\n",
				printHashes(cachedProof.Proof), cachedProofPos, p.String())
		}

		// And verify that the proof is correct.
		err = p.Verify(leafHashes, cachedProof)
		if err != nil {
			t.Fatal(err)
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
		currentLeaves := make([]hashAndPos, 0, len(leaves))
		for _, node := range p.NodeMap {
			currentLeaves = append(currentLeaves,
				hashAndPos{node.data, p.calculatePosition(node)})
		}
		// Sort to have a deterministic order of the currentLeaves. Since maps aren't
		// guaranteed to have the same order, we need to do this.
		sort.Slice(currentLeaves, func(a, b int) bool { return currentLeaves[a].pos < currentLeaves[b].pos })

		// Randomly grab some leaves.
		indexes := randomIndexes(len(currentLeaves), 2)
		leafSubset := make([]hashAndPos, len(indexes))
		for i := range leafSubset {
			leafSubset[i] = currentLeaves[indexes[i]]
		}
		// Generate a proof of the leafSubset.
		leafHashes := make([]Hash, len(leafSubset))
		for i := range leafHashes {
			leafHashes[i] = leafSubset[i].hash
		}
		cachedProof, err := p.Prove(leafHashes)
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
		leafHashes, cachedProof = UpdateProofAdd(cachedProof, nil, addHashes, nil, Stump{rootHashes, p.NumLeaves})

		beforePollardStr := p.String()
		// Modify the pollard.
		err = p.Modify(addLeaves, nil, nil)
		if err != nil {
			t.Fatal(err)
		}
		afterPollardStr := p.String()

		// And verify that the proof is correct.
		err = p.Verify(leafHashes, cachedProof)
		if err != nil {
			t.Fatalf("FuzzUpdateProofAdd Fail. Error:\n%v\nleafHashes:\n%s\nProof before:\n%s\n"+
				"Proof:\n%s\nPollard before:\n%s\nPollard after:\n%s\n",
				err, printHashes(leafHashes), proofBeforeStr, cachedProof.String(),
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

			newStump := Stump{make([]Hash, len(stump.Roots)), stump.NumLeaves}
			copy(newStump.Roots, stump.Roots)
			cachedHashes, cachedProof, err = UpdateProof(
				cachedProof, blockProof, cachedHashes, delHashes, addHashes, remembers, newStump)
			if err != nil {
				t.Fatal(err)
			}
			blockProof, err = p.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzModifyProof fail at block %d. Error: %v", b, err)
			}
			stump, err = UpdateStump(delHashes, addHashes, blockProof, stump)
			if err != nil {
				t.Fatal(err)
			}

			// Check that we have enough targets as we expect.
			if len(cachedProof.Targets) != len(cachedHashes) {
				t.Fatalf("FuzzUpdateProofRemove Fail. Expected %d "+
					"targets but got %d.\nDeleted hashes:\n%v."+
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
