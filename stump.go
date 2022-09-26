package utreexo

import (
	"encoding/hex"
	"fmt"
)

// Stump is bare-minimum data required to validate and update changes in the accumulator.
// Stump is client-side only and cannot generate proofs on its own. It can only validate
// them.
type Stump struct {
	// Roots are the state of the accumulator.
	Roots []Hash
	//  NumLeaves is how many leaves the accumulator has allocated for.
	NumLeaves uint64
}

// String returns the fields of stump in a human readable string.
func (s *Stump) String() string {
	str := fmt.Sprintf("NumLeaves: %d, ", s.NumLeaves)

	if len(s.Roots) == 1 {
		str += fmt.Sprintf("%d root: [", len(s.Roots))
	} else {
		str += fmt.Sprintf("%d roots: [", len(s.Roots))
	}
	for i, root := range s.Roots {
		str += hex.EncodeToString(root[:])

		if i != len(s.Roots)-1 {
			str += ", "
		}
	}
	str += "]"

	return str
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
// incrementing numLeaves. It also returns the intermediate hashes and their
// positions used to calculate the newly created roots.
func (s *Stump) add(adds []Hash) ([]Hash, []uint64, []uint64) {
	// afterRows is the total amount of rows after the addition has happened.
	afterRows := treeRows(s.NumLeaves + uint64(len(adds)))

	// allDeleted is all the empty roots that get deleted by the additions.
	allDeleted := rootsToDestory(uint64(len(adds)), s.NumLeaves, s.Roots)

	subTrees := make([]hashAndPos, 0, len(adds))
	for i, add := range adds {
		pos := s.NumLeaves

		// deleted is the empty roots that are being added over. These force
		// the current root to move up.
		deleted := rootsToDestory(uint64(len(adds)-i), s.NumLeaves, s.Roots)
		for _, del := range deleted {
			if isAncestor(parent(del, afterRows), pos, afterRows) {
				pos, _ = calcNextPosition(pos, del, afterRows)
			}
		}

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
		subTreeUpdated := hashAndPos{}
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
			if root != empty {
				subTreeUpdated.Append(leftSib(pos), root)
				subTreeUpdated.Append(pos, newRoot)

				// Calculate the hash of the new root and append it.
				newRoot = parentHash(root, newRoot)
				pos = parent(pos, afterRows)
			}
		}
		subTreeUpdated.Append(pos, newRoot)

		subTrees = append(subTrees, subTreeUpdated)
		s.Roots = append(s.Roots, newRoot)
		s.NumLeaves++
	}

	updated := hashAndPos{}
	for i, subTree := range subTrees {
		// If there are duplicates in the next subtree, skip the current subtree
		// as all the positions in this subtree will get added in the next subtree.
		if i+1 < len(subTrees) {
			duplicates := getHashAndPosHashSubset(subTree, subTrees[i+1].hashes)
			if duplicates.Len() > 0 {
				continue
			}
		}
		updated = mergeSortedHashAndPos(updated, subTree)
	}

	return updated.hashes, updated.positions, allDeleted
}

// rootsToDestory returns the empty roots that get written over after numAdds
// amount of leaves have been added.
func rootsToDestory(numAdds, numLeaves uint64, origRoots []Hash) []uint64 {
	roots := make([]Hash, len(origRoots))
	copy(roots, origRoots)

	deleted := make([]uint64, 0, treeRows(numLeaves+numAdds))
	for i := uint64(0); i < numAdds; i++ {
		for h := uint8(0); (numLeaves>>h)&1 == 1; h++ {
			root := roots[len(roots)-1]
			roots = roots[:len(roots)-1]
			if root == empty {
				rootPos := rootPosition(numLeaves, h, treeRows(numLeaves+(numAdds-i)))
				deleted = append(deleted, rootPos)
			}
		}
		// Just adding a non-zero value to the slice.
		roots = append(roots, Hash{1})
		numLeaves++
	}

	return deleted
}
