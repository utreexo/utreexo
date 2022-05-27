package utreexo

import "fmt"

// Stump is bare-minimum data required to validate and update changes in the accumulator.
// Stump is client-side only and cannot generate proofs on its own. It can only validate
// them.
type Stump struct {
	// Roots are the state of the accumulator.
	Roots []Hash
	//  NumLeaves is how many leaves the accumulator has allocated for.
	NumLeaves uint64
}

// UpdateStump verifies the proof and returns a new Stump that is updated with
// additions and the deletions.
func UpdateStump(delHashes, addHashes []Hash, proof Proof, stump Stump) (Stump, error) {
	rootCandidates, err := StumpVerify(stump, delHashes, proof)
	if err != nil {
		return Stump{}, fmt.Errorf("UpdateStump fail: Invalid proof. Error: %s", err)
	}

	modifiedRoots := stumpDel(stump.NumLeaves, proof)

	roots := make([]Hash, len(stump.Roots))
	idx := 0
	for i := len(stump.Roots) - 1; i >= 0; i-- {
		root := stump.Roots[i]

		if idx < len(rootCandidates) && root == rootCandidates[idx] {
			roots[i] = modifiedRoots[idx]
			idx++
		} else {
			roots[i] = stump.Roots[i]
		}
	}

	return stumpAdd(Stump{roots, stump.NumLeaves}, addHashes), nil
}

// StumpVerify verifies the proof passed in against the passed in stump. The returned hashes
// are the hashes that were calculated from the proof.
func StumpVerify(stump Stump, delHashes []Hash, proof Proof) ([]Hash, error) {
	if len(delHashes) != len(proof.Targets) {
		return nil, fmt.Errorf("StumpVerify fail. Was given %d targets but got %d hashes",
			len(proof.Targets), len(delHashes))
	}

	rootCandidates := calculateRoots(stump.NumLeaves, delHashes, proof)
	rootMatches := 0
	for i := range stump.Roots {
		if len(rootCandidates) > rootMatches &&
			stump.Roots[len(stump.Roots)-(i+1)] == rootCandidates[rootMatches] {
			rootMatches++
		}
	}

	if len(rootCandidates) != rootMatches {
		// The proof is invalid because some root candidates were not
		// included in `roots`.
		err := fmt.Errorf("StumpVerify fail. Invalid proof. Have %d roots but only "+
			"matched %d roots", len(rootCandidates), rootMatches)
		return nil, err
	}

	return rootCandidates, nil
}

// stumpDel calculates the modified roots effected by the deletion.
func stumpDel(numLeaves uint64, proof Proof) []Hash {
	delHashes, afterProof := proofAfterDeletion(numLeaves, proof)
	roots := calculateRoots(numLeaves, delHashes, afterProof)
	return roots
}

// stumpAdd returns a new Stump after adding the passed in adds to the previous roots
// and numLeaves.
func stumpAdd(stump Stump, adds []Hash) Stump {
	for _, add := range adds {
		// We can tell where the roots are by looking at the binary representation
		// of the numLeaves. Wherever there's a 1, there's a root.
		//
		// numLeaves of 8 will be '1000' in binary, so there will be one root at
		// row 3. numLeaves of 3 will be '11' in binary, so there's two roots. One at
		// row 0 and one at row 1.
		//
		// In this loop below, we're looking for these roots by checking if there's
		// a '1'. If there is a '1', we'll hash the root being added with that root
		// until we hit a '0'.
		newRoot := add
		for h := uint8(0); (stump.NumLeaves>>h)&1 == 1; h++ {
			root := stump.Roots[len(stump.Roots)-1]
			stump.Roots = stump.Roots[:len(stump.Roots)-1]

			// If the root that we're gonna hash with is empty, move the current
			// node up to the position of the parent.
			//
			// Example:
			//
			// 12
			// |-------\
			// 08      09
			// |---\   |---\
			// 00  01  02  03  --
			//
			// When we add 05 to this tree, 04 is empty so we move 05 to 10.
			// The resulting tree looks like below. The hash at position 10
			// is not hash(04 || 05) but just the hash of 05.
			//
			// 12
			// |-------\
			// 08      09      10
			// |---\   |---\   |---\
			// 00  01  02  03  --  --
			if root == empty {
				continue
			} else {
				// Calculate the hash of the new root and append it.
				newRoot = parentHash(root, newRoot)
			}
		}
		stump.Roots = append(stump.Roots, newRoot)
		stump.NumLeaves++
	}

	return stump
}
