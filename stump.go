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

// Update verifies the proof and updates the Stump with the additions and the deletions.
func (s *Stump) Update(delHashes, addHashes []Hash, proof Proof) error {
	// Delete then add.
	err := s.del(delHashes, proof)
	if err != nil {
		return err
	}
	s.add(addHashes)

	return nil
}

// Verify verifies the proof passed in against the passed in stump. The returned ints
// are the indexes of the roots that were matched with the roots calculated from
// the proof.
func Verify(stump Stump, delHashes []Hash, proof Proof) ([]int, error) {
	if len(delHashes) != len(proof.Targets) {
		return nil, fmt.Errorf("Verify fail. Was given %d targets but got %d "+
			"hashes for those targets", len(proof.Targets), len(delHashes))
	}

	_, rootCandidates := calculateHashes(stump.NumLeaves, delHashes, proof)
	rootIndexes := make([]int, 0, len(rootCandidates))
	for i := range stump.Roots {
		if len(rootCandidates) > len(rootIndexes) &&
			stump.Roots[len(stump.Roots)-(i+1)] == rootCandidates[len(rootIndexes)] {

			rootIndexes = append(rootIndexes, len(stump.Roots)-(i+1))
		}
	}

	if len(rootCandidates) != len(rootIndexes) {
		// The proof is invalid because some root candidates were not
		// included in `roots`.
		err := fmt.Errorf("StumpVerify fail. Invalid proof. Have %d roots but only "+
			"matched %d roots", len(rootCandidates), len(rootIndexes))
		return nil, err
	}

	return rootIndexes, nil
}

// del verifies that the passed in proof is correct. Then it calculates the
// modified roots effected by the deletion and updates the roots of the stump
// accordingly.
func (s *Stump) del(delHashes []Hash, proof Proof) error {
	// First verify the proof to make sure it's correct.
	rootIndexes, err := Verify(*s, delHashes, proof)
	if err != nil {
		return fmt.Errorf("Stump update fail: Invalid proof. Error: %s", err)
	}

	// Then calculate the modified roots.
	_, modifiedRoots := calculateHashes(s.NumLeaves, nil, proof)
	if len(modifiedRoots) != len(rootIndexes) {
		return fmt.Errorf("Stump update fail: expected %d modified roots but got %d",
			len(rootIndexes), len(modifiedRoots))
	}

	// Update the modified roots.
	for i, index := range rootIndexes {
		s.Roots[index] = modifiedRoots[i]
	}

	return nil
}

// add adds the passed in hashes to accumulator, adding new roots and
// incrementing numLeaves.
func (s *Stump) add(adds []Hash) {
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
		for h := uint8(0); (s.NumLeaves>>h)&1 == 1; h++ {
			root := s.Roots[len(s.Roots)-1]
			s.Roots = s.Roots[:len(s.Roots)-1]

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
		s.Roots = append(s.Roots, newRoot)
		s.NumLeaves++
	}
}
