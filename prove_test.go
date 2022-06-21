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
	proofPos, _ := proofPositions(proof.Targets, p.numLeaves, treeRows(p.numLeaves))
	currentHashes := toHashAndPos(proofPos, proof.Proof)
	// Append the needed hashes to the proof.
	currentHashes = append(currentHashes, neededHashes...)

	// As new targets are added, we're able to calulate positions that we couldn't before. These positions
	// may already exist as proofs. Remove these as duplicates are not expected during proof verification.
	_, calculateables := proofPositions(desiredPositions, p.numLeaves, treeRows(p.numLeaves))
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
		leaves, delHashes, delPos := getAddsAndDels(uint32(p.numLeaves), startLeaves, delCount)
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
		for _, node := range p.nodeMap {
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
		missingPositions := GetMissingPositions(p.numLeaves, proof.Targets, desiredPositions)

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
		for _, node := range p.nodeMap {
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
		newproof := RemoveTargets(p.numLeaves, leafHashes, proof, positions)
		newDelHashes := make([]Hash, len(newproof.Targets))
		for i := range newDelHashes {
			newDelHashes[i] = p.getHash(newproof.Targets[i])
			if newDelHashes[i] == empty {
				t.Fatalf("FuzzRemoveTargets fail: Couldn't grab the hash "+
					"for target %d", newproof.Targets[i])
			}
		}

		err = p.Verify(newDelHashes, newproof)
		if err != nil {
			t.Fatalf("FuzzRemoveTargets fail. Error: %v\n\nWas removing targets:\n%v\n"+
				"from proof:\n%s\nGot proof:\n%s\nPollard:\n%s", err,
				positions, proof.String(), newproof.String(), p.String())
		}
	})
}

func TestModifyProof(t *testing.T) {
	// Create the starting off pollard.
	adds := make([]Leaf, 8)
	for i := range adds {
		adds[i].Hash[0] = uint8(i + 1)
	}
	p := NewAccumulator(true)

	err := p.Modify(adds, nil, nil)
	if err != nil {
		t.Fatal(err)
	}

	fmt.Println(p.String())

	proof1, err := p.Prove([]Hash{{8}})
	if err != nil {
		t.Fatal(err)
	}

	fmt.Println("cached proof:\n", proof1.String())

	modifyProof, err := p.Prove([]Hash{{1}, {3}})
	if err != nil {
		t.Fatal(err)
	}

	err = p.Modify(nil, []Hash{{1}, {3}}, []uint64{0, 2})
	if err != nil {
		t.Fatal(err)
	}
	fmt.Println(p.String())

	proof2 := ModifyProof(proof1, modifyProof, []Hash{{8}}, p.numLeaves)
	fmt.Println("after modify:\n", proof2.String())
}
