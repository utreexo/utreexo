package utreexo

import (
	"encoding/hex"
	"fmt"
	"sort"

	"golang.org/x/exp/slices"
)

// Proof is the inclusion-proof for multiple leaves.
type Proof struct {
	// Targets are the ist of leaf locations to delete and they are the bottommost leaves.
	// With the tree below, the Targets can only consist of one of these: 02, 03, 04.
	//
	// 06
	// |-------\
	// 04      05
	// |---\   |---\
	//         02  03
	Targets []uint64

	// All the nodes in the tree that are needed to hash up to the root of
	// the tree. Here, the root is 06. If Targets are [00, 01], then Proof
	// would be [05] as you need 04 and 05 to hash to 06. 04 can be calculated
	// by hashing 00 and 01.
	//
	// 06
	// |-------\
	// 04      05
	// |---\   |---\
	// 00  01  02  03
	Proof []Hash
}

// String returns a string of the proof. Useful for debugging.
func (p *Proof) String() string {
	s := fmt.Sprintf("%d targets: ", len(p.Targets))
	for _, t := range p.Targets {
		s += fmt.Sprintf("%d ", t)
	}
	s += fmt.Sprintf("\n%d proofs: ", len(p.Proof))
	for _, p := range p.Proof {
		s += fmt.Sprintf("%04x\t", p[:8])
	}
	s += "\n"
	return s
}

func (p *Pollard) Prove(hashes []Hash) (Proof, error) {
	// No hashes to prove means that the proof is empty. An empty
	// pollard also has an empty proof.
	if len(hashes) == 0 || p.NumLeaves == 0 {
		return Proof{}, nil
	}
	// A Pollard with 1 leaf has no proof and only 1 target.
	if p.NumLeaves == 1 {
		return Proof{Targets: []uint64{0}}, nil
	}

	var proof Proof
	proof.Targets = make([]uint64, len(hashes))

	// Grab the positions of the hashes that are to be proven.
	for i, wanted := range hashes {
		node, ok := p.NodeMap[wanted.mini()]
		if !ok {
			return proof, fmt.Errorf("Prove error: hash %s not found",
				hex.EncodeToString(wanted[:]))
		}
		proof.Targets[i] = p.calculatePosition(node)
	}

	// Sort the targets as the proof hashes need to be sorted.
	//
	// TODO find out if sorting and losing in-block position information hurts
	// locality or performance.
	sortedTargets := make([]uint64, len(proof.Targets))
	copy(sortedTargets, proof.Targets)
	sort.Slice(sortedTargets, func(a, b int) bool { return sortedTargets[a] < sortedTargets[b] })

	// Get the positions of all the hashes that are needed to prove the targets
	proofPositions, _ := proofPositions(sortedTargets, p.NumLeaves, treeRows(p.NumLeaves))

	// Fetch all the proofs from the accumulator.
	proof.Proof = make([]Hash, len(proofPositions))
	for i, proofPos := range proofPositions {
		hash := p.getHash(proofPos)
		if hash == empty {
			return Proof{}, fmt.Errorf("Prove error: couldn't read position %d", proofPos)
		}
		proof.Proof[i] = hash
	}

	return proof, nil
}

// hashAndPos provides a type to manipulate both the corresponding positions
// and the hashes at the same time.
type hashAndPos struct {
	positions []uint64
	hashes    []Hash
}

// toHashAndPos returns the slice of hash and positions that's sorted by
// by the positions.
//
// NOTE: the length of the targets and the hashes must be of the same length.
// There are no checks for this and it's the caller's responsibility.
func toHashAndPos(origTargets []uint64, origHashes []Hash) hashAndPos {
	targets := make([]uint64, len(origTargets))
	copy(targets, origTargets)

	hashes := make([]Hash, len(origHashes))
	copy(hashes, origHashes)
	hnp := hashAndPos{targets, hashes}

	// No guarantee that the targets and the delHashes are in order. Sort them
	// before processing.
	sort.Sort(hnp)

	return hnp
}

// Len returns the length of the slices.
// Implements the sort.Sort interface.
func (hnp hashAndPos) Len() int {
	return len(hnp.positions)
}

// Swap swaps the elements at the specified indexes.
// Implements the sort.Sort interface.
func (hnp hashAndPos) Swap(i, j int) {
	hnp.positions[i], hnp.positions[j] = hnp.positions[j], hnp.positions[i]
	hnp.hashes[i], hnp.hashes[j] = hnp.hashes[j], hnp.hashes[i]
}

// Less returns if the position at index i is less and the position at index j.
// Implements the sort.Sort interface.
func (hnp hashAndPos) Less(i, j int) bool {
	return hnp.positions[i] < hnp.positions[j]
}

// Append appends the given position and the hash to each of the slices.
func (hnp *hashAndPos) Append(position uint64, hash Hash) {
	hnp.positions = append(hnp.positions, position)
	hnp.hashes = append(hnp.hashes, hash)
}

// AppendMany appends the given slices of positions and the hashes
// to the hashAndPos.
func (hnp *hashAndPos) AppendMany(positions []uint64, hashes []Hash) {
	hnp.positions = append(hnp.positions, positions...)
	hnp.hashes = append(hnp.hashes, hashes...)
}

// Delete deletes the hash and the position at index i.
func (hnp *hashAndPos) Delete(i int) {
	hnp.positions = append(hnp.positions[:i], hnp.positions[i+1:]...)
	hnp.hashes = append(hnp.hashes[:i], hnp.hashes[i+1:]...)
}

// PopFront pops the first off element from the slice.
func (hnp *hashAndPos) PopFront() (uint64, Hash) {
	var pos uint64
	var hash Hash
	pos, hnp.positions = hnp.positions[0], hnp.positions[1:]
	hash, hnp.hashes = hnp.hashes[0], hnp.hashes[1:]

	return pos, hash
}

// Pop pops off the last element from the slice.
func (hnp *hashAndPos) Pop() (uint64, Hash) {
	var pos uint64
	var hash Hash
	pos, hnp.positions = hnp.positions[len(hnp.positions)-1], hnp.positions[:len(hnp.positions)-1]
	hash, hnp.hashes = hnp.hashes[len(hnp.hashes)-1], hnp.hashes[:len(hnp.hashes)-1]

	return pos, hash
}

// Reset resets the slice of positions and the hashes for this hashAndPos.
func (hnp *hashAndPos) Reset() {
	hnp.positions = hnp.positions[:0]
	hnp.hashes = hnp.hashes[:0]
}

// String returns the hashAndPos as a readable string. Useful for debugging.
func (hnp hashAndPos) String() string {
	str := fmt.Sprintf("Positions: %v\n", hnp.positions)
	str += "Hashes:\n"
	for _, hash := range hnp.hashes {
		str += fmt.Sprintf("%s\n", hex.EncodeToString(hash[:]))
	}

	return str
}

// mergeSortedHashAndPos allocates and returns a new merged hashAndPos created from
// the passed in hashAndPoses.
func mergeSortedHashAndPos(a, b hashAndPos) (c hashAndPos) {
	maxa := a.Len()
	maxb := b.Len()

	// shortcuts:
	if maxa == 0 {
		c.positions = make([]uint64, maxb)
		copy(c.positions, b.positions)

		c.hashes = make([]Hash, maxb)
		copy(c.hashes, b.hashes)
		return c
	}
	if maxb == 0 {
		c.positions = make([]uint64, maxa)
		copy(c.positions, a.positions)

		c.hashes = make([]Hash, maxa)
		copy(c.hashes, a.hashes)
		return c
	}

	// make it (potentially) too long and truncate later
	c.hashes = make([]Hash, maxa+maxb)
	c.positions = make([]uint64, maxa+maxb)

	idxa, idxb := 0, 0
	for j := 0; j < c.Len(); j++ {
		// if we're out of a or b, just use the remainder of the other one
		if idxa >= maxa {
			// a is done, copy remainder of b
			copy(c.positions[j:], b.positions[idxb:])
			j += copy(c.hashes[j:], b.hashes[idxb:])

			c.positions = c.positions[:j] // truncate empty section of c
			c.hashes = c.hashes[:j]       // truncate empty section of c
			break
		}
		if idxb >= maxb {
			// b is done, copy remainder of a
			copy(c.positions[j:], a.positions[idxa:])
			j += copy(c.hashes[j:], a.hashes[idxa:])

			c.positions = c.positions[:j] // truncate empty section of c
			c.hashes = c.hashes[:j]       // truncate empty section of c
			break
		}

		vala, valb := a.positions[idxa], b.positions[idxb]
		if vala < valb { // a is less so append that
			c.positions[j] = vala
			c.hashes[j] = a.hashes[idxa]
			idxa++
		} else if vala > valb { // b is less so append that
			c.positions[j] = valb
			c.hashes[j] = b.hashes[idxb]
			idxb++
		} else { // they're equal
			c.positions[j] = vala
			c.hashes[j] = a.hashes[idxa]
			idxa++
			idxb++
		}
	}

	return
}

// subtractSortedHashAndPos subtracts all the positions and the corresponding hashes in b from a.
func subtractSortedHashAndPos[E any](a hashAndPos, b []E, cmp func(uint64, E) int) hashAndPos {
	bIdx := 0
	for i := 0; i < a.Len(); i++ {
		if bIdx >= len(b) {
			break
		}
		res := cmp(a.positions[i], b[bIdx])
		// If a[i] == b[bIdx], remove the element from a.
		if res == 0 {
			a.positions = append(a.positions[:i], a.positions[i+1:]...)
			a.hashes = append(a.hashes[:i], a.hashes[i+1:]...)
			bIdx++
			i--
		} else if res == -1 {
			// a[i] < b[bIdx]
			continue
		} else if res == 1 {
			// a[i] > b[bIdx]
			bIdx++
			i--
		}
	}

	return a
}

// removeHashesFromHashAndPos removes the hashes and the corresponding positions from slice1.
func removeHashesFromHashAndPos[E any](slice1 hashAndPos, slice2 []E, getHash func(elem E) Hash) hashAndPos {
	allKeys := make(map[Hash]bool, len(slice2))
	for _, elem := range slice2 {
		allKeys[getHash(elem)] = true
	}

	retSlice := hashAndPos{}
	retSlice.positions = make([]uint64, 0, slice1.Len())
	retSlice.hashes = make([]Hash, 0, slice1.Len())
	for i := 0; i < slice1.Len(); i++ {
		elemHash := slice1.hashes[i]
		elemPos := slice1.positions[i]

		if _, val := allKeys[elemHash]; !val {
			retSlice.Append(elemPos, elemHash)
		}
	}

	return retSlice
}

// Verify calculates the root hashes from the passed in proof and delHashes and
// compares it against the current roots in the pollard.
func (p *Pollard) Verify(delHashes []Hash, proof Proof) error {
	if len(delHashes) == 0 {
		return nil
	}

	if len(delHashes) != len(proof.Targets) {
		return fmt.Errorf("Pollard.Verify fail. Was given %d targets but got %d hashes",
			len(proof.Targets), len(delHashes))
	}

	rootCandidates := calculateRoots(p.NumLeaves, delHashes, proof)
	if len(rootCandidates) == 0 {
		return fmt.Errorf("Pollard.Verify fail. No roots calculated "+
			"but have %d deletions", len(delHashes))
	}

	rootMatches := 0
	for i := range p.Roots {
		if len(rootCandidates) > rootMatches &&
			p.Roots[len(p.Roots)-(i+1)].data == rootCandidates[rootMatches] {
			rootMatches++
		}
	}
	// Error out if all the rootCandidates do not have a corresponding
	// polnode with the same hash.
	if len(rootCandidates) != rootMatches {
		rootHashes := make([]Hash, len(p.Roots))
		for i := range rootHashes {
			rootHashes[i] = p.Roots[i].data
		}
		// The proof is invalid because some root candidates were not
		// included in `roots`.
		err := fmt.Errorf("Pollard.Verify fail. Have %d roots but only "+
			"matched %d roots.\nRootcandidates:\n%v\nRoots:\n%v",
			len(rootCandidates), rootMatches,
			printHashes(rootCandidates), printHashes(rootHashes))
		return err
	}

	return nil
}

// getNextLeast returns the index of the slice containing the lesser element in
// the front of the slice. If both slices are empty, -1 is returned.
func getNextLeast[E any](slice1, slice2 []E, less func(a, b E) bool) int {
	if len(slice1) > 0 && len(slice2) > 0 {
		if less(slice1[0], slice2[0]) {
			return 0
		} else {
			return 1
		}
	} else if len(slice1) > 0 && len(slice2) == 0 {
		return 0
	} else if len(slice1) == 0 && len(slice2) > 0 {
		return 1
	}

	return -1
}

// calculateRoots calculates and returns the root hashes. Passing nil delHashes will
// return the roots after the deletion of the targets.
func calculateRoots(numLeaves uint64, delHashes []Hash, proof Proof) []Hash {
	totalRows := treeRows(numLeaves)

	// Where all the root hashes that we've calculated will go to.
	calculatedRootHashes := make([]Hash, 0, numRoots(numLeaves))

	// Where all the parent hashes we've calculated in a given row will go to.
	nextProves := hashAndPos{make([]uint64, 0, len(proof.Targets)), make([]Hash, 0, len(proof.Targets))}

	// If delHashes are nil, it means that we're calculating the roots after del.
	if delHashes == nil {
		delHashes = make([]Hash, len(proof.Targets))
	}

	// These are the leaves to be proven. Each represent a position and the
	// hash of a leaf.
	toProve := toHashAndPos(proof.Targets, delHashes)

	// Separate index for the hashes in the passed in proof.
	proofHashIdx := 0
	for row := uint8(0); row <= totalRows; {
		// Grab the next position and hash to process.
		var provePos uint64
		var proveHash Hash
		idx := getNextLeast(toProve.positions, nextProves.positions, uint64Less)
		if idx == 0 {
			provePos, proveHash = toProve.PopFront()
		} else if idx == 1 {
			provePos, proveHash = nextProves.PopFront()
		} else {
			// Break if we don't have anymore elements left.
			break
		}

		// Keep incrementing the row if the current position is greater
		// than the max position on this row.
		//
		// Cannot error out here because this loop already checks that
		// row is lower than totalRows.
		maxPos, _ := maxPositionAtRow(row, totalRows, numLeaves)
		for provePos > maxPos {
			row++
			maxPos, _ = maxPositionAtRow(row, totalRows, numLeaves)
		}

		// This means we hashed all the way to the top of this subtree.
		if isRootPositionOnRow(provePos, numLeaves, row, totalRows) {
			calculatedRootHashes = append(calculatedRootHashes, proveHash)
			continue
		}

		// Attempt to grab the sibling of the current position and hash to process.
		maybeSibHash, sibPresent := empty, false
		idx = getNextLeast(toProve.positions, nextProves.positions, uint64Less)
		if idx == 0 {
			if rightSib(provePos) == toProve.positions[0] {
				sibPresent = true
				_, maybeSibHash = toProve.PopFront()
			}
		} else if idx == 1 {
			if rightSib(provePos) == nextProves.positions[0] {
				sibPresent = true
				_, maybeSibHash = nextProves.PopFront()
			}
		}

		// Calculate the next hash.
		var nextHash Hash
		if sibPresent {
			// There's 3 different outcomes if the next rowTarget
			// is a sibling to the current one.
			//
			// Either sibling can be a target, which the other
			// sibling moves up in that case. If neither are
			// a target, then we hash to calculate the parent.
			if proveHash == empty {
				nextHash = maybeSibHash
			} else if maybeSibHash == empty {
				nextHash = proveHash
			} else {
				nextHash = parentHash(proveHash, maybeSibHash)
			}
		} else {
			// If the next prove isn't the sibling of this prove, we fetch
			// the next proof hash to calculate the parent.
			hash := proof.Proof[proofHashIdx]
			proofHashIdx++

			nextHash = hash
			if proveHash != empty {
				if isLeftNiece(provePos) {
					nextHash = parentHash(proveHash, hash)
				} else {
					nextHash = parentHash(hash, proveHash)
				}
			}
		}

		nextProves.Append(parent(provePos, totalRows), nextHash)
	}

	return calculatedRootHashes
}

func mergeSortedSlicesFunc[E any](a, b []E, cmp func(E, E) int) (c []E) {
	maxa := len(a)
	maxb := len(b)

	// shortcuts:
	if maxa == 0 {
		c = make([]E, maxb)
		copy(c, b)
		return c
	}
	if maxb == 0 {
		c = make([]E, maxa)
		copy(c, a)
		return c
	}

	// make it (potentially) too long and truncate later
	c = make([]E, maxa+maxb)

	idxa, idxb := 0, 0
	for j := 0; j < len(c); j++ {
		// if we're out of a or b, just use the remainder of the other one
		if idxa >= maxa {
			// a is done, copy remainder of b
			j += copy(c[j:], b[idxb:])
			c = c[:j] // truncate empty section of c
			break
		}
		if idxb >= maxb {
			// b is done, copy remainder of a
			j += copy(c[j:], a[idxa:])
			c = c[:j] // truncate empty section of c
			break
		}

		vala, valb := a[idxa], b[idxb]
		if cmp(vala, valb) == -1 { // a is less so append that
			c[j] = vala
			idxa++
		} else if cmp(vala, valb) == 1 { // b is less so append that
			c[j] = valb
			idxb++
		} else { // they're equal
			c[j] = vala
			idxa++
			idxb++
		}
	}

	return
}

// removeDuplicateUint64Func removes duplicates from the slice.
func removeDuplicateUint64Func[E any](slice []E, get func(E) uint64) []E {
	allKeys := make(map[uint64]bool)
	list := []E{}
	for _, item := range slice {
		if _, value := allKeys[get(item)]; !value {
			allKeys[get(item)] = true
			list = append(list, item)
		}
	}
	return list
}

// removeHashes returns a newly allocated slice with all only elements
// that exist uniquely in slice1 (and not in slice2).
// Basically returns a new slice that's slice1 - slice2.
func removeHashes[E any](slice1, slice2 []E, getHash func(elem E) Hash) []E {
	allKeys := make(map[Hash]bool, len(slice2))
	for _, elem := range slice2 {
		allKeys[getHash(elem)] = true
	}

	retSlice := make([]E, 0, len(slice1))
	for i := 0; i < len(slice1); i++ {
		elem := slice1[i]

		if _, val := allKeys[getHash(elem)]; !val {
			retSlice = append(retSlice, elem)
		}
	}
	return retSlice
}

// subtractSortedSlice removes all elements of b from a. It returns a slice of a-b.
// Both slices MUST be sorted.
func subtractSortedSlice[E, F any](a []E, b []F, cmp func(E, F) int) []E {
	bIdx := 0
	for i := 0; i < len(a); i++ {
		if bIdx >= len(b) {
			break
		}
		res := cmp(a[i], b[bIdx])
		// If a[i] == b[bIdx], remove the element from a.
		if res == 0 {
			a = append(a[:i], a[i+1:]...)
			bIdx++
			i--
		} else if res == -1 {
			// a[i] < b[bIdx]
			continue
		} else if res == 1 {
			// a[i] > b[bIdx]
			bIdx++
			i--
		}
	}

	return a
}

// proofAfterDeletion modifies the proof so that it proves the siblings of the targets
// in this proof. Having this information allows for the calculation of roots after the
// deletion has happened.
func proofAfterDeletion(numLeaves uint64, proof Proof) ([]Hash, Proof) {
	// We don't need the delHashes for the proof if we're deleting every target.
	// Create these empty delHashes are needed since proofAfterPartialDeletion
	// needs it for making hashAndPos for the targets.
	delHashes := make([]Hash, len(proof.Targets))
	return proofAfterPartialDeletion(numLeaves, proof, delHashes, proof.Targets)
}

// proofAfterDeletion modifies the proof so that it proves the siblings of the targets
// remTargets. The hashes and proof returned for the calculation of roots after the
// deletion of the remTargets has happened.
//
// NOTE: remTargets must be a subset of proof.Targets. Otherwise nothing happens.
func proofAfterPartialDeletion(numLeaves uint64, proof Proof, delHashes []Hash, remTargets []uint64) ([]Hash, Proof) {
	forestRows := treeRows(numLeaves)

	// Copy the targets to avoid mutating the original. Then detwin it
	// to prep for deletion.
	targets := copySortedFunc(proof.Targets, uint64Less)

	// Use the sorted targets to generate the positions for the proof hashes.
	proofPos, _ := proofPositions(targets, numLeaves, forestRows)
	// Attach a position to each of the proof hashes.
	hnp := toHashAndPos(proofPos, proof.Proof)

	targetsWithHashes := toHashAndPos(proof.Targets, delHashes)

	// We want to detwin targetsWithHashes but *only* the targets that will be removed. We
	// do this by removing the remTargets, detwining the remTargets, then adding back the
	// detwined remTargets to the targetsWithHashes.
	sort.Slice(remTargets, func(a, b int) bool { return remTargets[a] < remTargets[b] })
	targetsWithHashes = subtractSortedHashAndPos(targetsWithHashes, remTargets, uint64Cmp)

	// Detwin the removes.
	deTwinedRems := make([]uint64, len(remTargets))
	copy(deTwinedRems, remTargets)
	deTwinedRems = deTwin(deTwinedRems, forestRows)

	// Final step of the detwin. Add the detwined target and hash to targetsWithHashes.
	// Empty hashes are just so that they can also be hashAndPos. All of these will get
	// removed and be replaced with the sibling so it's ok with have empty hashes.
	deTwinedRemsWithHash := toHashAndPos(deTwinedRems, make([]Hash, len(deTwinedRems)))
	targetsWithHashes = mergeSortedHashAndPos(targetsWithHashes, deTwinedRemsWithHash)

	// For each of the detwinedRems, if we find it in targetsWithHashes, we'll try
	// to find the sibling in the proof hashes and promote it as the parent. If
	// it's not in the proof hashes, we'll move the descendants of the existing
	// proofs of the sibling's parent up by one row.
	for i := 0; i < len(deTwinedRems); i++ {
		// If this deletion isn't in the targets, move on.
		idx := slices.IndexFunc(targetsWithHashes.positions, func(elem uint64) bool { return elem == deTwinedRems[i] })
		if idx == -1 {
			continue
		}
		targetPos := targetsWithHashes.positions[idx]
		targetsWithHashes.Delete(idx)

		// If we're deleting a root, then add empty to the targets and move on.
		if isRootPosition(deTwinedRems[i], numLeaves, forestRows) {
			targetsWithHashes = mergeSortedHashAndPos(targetsWithHashes, hashAndPos{[]uint64{deTwinedRems[i]}, []Hash{empty}})
			continue
		}

		// Same for whenthe sibling is a root. Add empty and move on.
		sib := sibling(targetPos)
		if isRootPosition(sib, numLeaves, forestRows) {
			targetsWithHashes = mergeSortedHashAndPos(targetsWithHashes, hashAndPos{[]uint64{sib}, []Hash{empty}})
			continue
		}

		// Look for the sibling in the proof hashes.
		if idx := slices.IndexFunc(hnp.positions, func(elem uint64) bool { return elem == sib }); idx != -1 {
			parentPos := parent(sib, forestRows)

			targetsWithHashes = mergeSortedHashAndPos(targetsWithHashes, hashAndPos{[]uint64{parentPos}, []Hash{hnp.hashes[idx]}})

			// Delete the sibling from hnp as this sibling is a target now, not a proof.
			hnp.Delete(idx)
		} else {
			// If the sibling is not in the proof hashes or the targets,
			// the descendants of the sibling will be moving up.
			//
			// 14
			// |---------------\
			// 12              13
			// |-------\       |-------\
			// 08      09      10      11
			// |---\   |---\   |---\   |---\
			// 00  01          04  05  06  07
			//
			// In the above tree, if we're deleting 00 and 09, 09 won't be
			// able to find the sibling in the proof hashes. 01 would have moved
			// up to 08 and we'll move 08 up and to 12 as 09 is also being deleted.

			// First update the targets to their new positions.
			for j := targetsWithHashes.Len() - 1; j >= 0; j-- {
				ancestor := isAncestor(parent(sib, forestRows), targetsWithHashes.positions[j], forestRows)
				if ancestor {
					// We can ignore the error since we've already verified that
					// the targetsWithHashes[j] is an ancestor of sib.
					nextPos, _ := calcNextPosition(targetsWithHashes.positions[j], sib, forestRows)
					targetsWithHashes.positions[j] = nextPos
				}
			}

			// Update the proofs as well.
			for j := hnp.Len() - 1; j >= 0; j-- {
				ancestor := isAncestor(parent(sib, forestRows), hnp.positions[j], forestRows)
				if ancestor {
					// We can ignore the error since we've already verified that
					// the hnp[j] is an ancestor of sib.
					nextPos, _ := calcNextPosition(hnp.positions[j], sib, forestRows)
					hnp.positions[j] = nextPos
				}
			}

			// Dedupe.
			sort.Sort(targetsWithHashes)
			for i := 0; i < targetsWithHashes.Len(); i++ {
				if i < targetsWithHashes.Len()-1 && targetsWithHashes.positions[i] == targetsWithHashes.positions[i+1] {
					targetsWithHashes.Delete(i)
				}
			}
		}
	}

	// The proof hashes should be in order before they're included in the proof.
	sort.Sort(hnp)

	return targetsWithHashes.hashes, Proof{targetsWithHashes.positions, hnp.hashes}
}

// GetMissingPositions returns the positions missing in the proof to proof the desiredTargets.
//
// The proofTargets being passed in MUST be a from a valid proof. Having an invalid proof may
// result in errors.
//
// The passed in desiredTargets also MUST be a valid position in the accumulator. There are
// no checks to make sure the desiredTargets exist in the accumulator so the caller must
// check that they indeed do exist.
func GetMissingPositions(numLeaves uint64, proofTargets, desiredTargets []uint64) []uint64 {
	forestRows := treeRows(numLeaves)

	// Copy the targets to avoid mutating the original. Then detwin it
	// to prep for deletion.
	targets := make([]uint64, len(proofTargets))
	copy(targets, proofTargets)

	// Targets and the desiredTargets need to be sorted.
	sort.Slice(targets, func(a, b int) bool { return targets[a] < targets[b] })
	sort.Slice(desiredTargets, func(a, b int) bool { return desiredTargets[a] < desiredTargets[b] })

	// Check for the targets that we already have and remove them from the desiredTargets.
	desiredTargets = subtractSortedSlice(desiredTargets, targets, uint64Cmp)

	// Return early if we don't have any targets to prove.
	if len(desiredTargets) <= 0 {
		return nil
	}

	// desiredPositions are all the positions that are needed to proof the desiredTargets.
	desiredPositions, _ := proofPositions(desiredTargets, numLeaves, forestRows)

	// havePositions represent all the positions in the tree we already have access to.
	// Since targets and computablePositions are something we already have, append
	// those to the havePositions.
	havePositions, computablePos := proofPositions(targets, numLeaves, forestRows)
	havePositions = append(havePositions, targets...)
	havePositions = append(havePositions, computablePos...)
	sort.Slice(havePositions, func(a, b int) bool { return havePositions[a] < havePositions[b] })

	// Get rid of any positions that we already have.
	desiredPositions = subtractSortedSlice(desiredPositions, havePositions, uint64Cmp)

	return desiredPositions
}

// hashSiblings hashes the parent hash of the given hnp and sibHash and then tries to find all
// the siblings of the resulting parent
func hashSiblings(proofHashes hashAndPos, pos uint64, currentHash, sibHash Hash, forestRows uint8) hashAndPos {
	// Calculate the parent hash and the position.
	var hash Hash
	if isLeftNiece(pos) {
		hash = parentHash(currentHash, sibHash)
	} else {
		hash = parentHash(sibHash, currentHash)
	}
	pos = parent(pos, forestRows)
	proofHashes.Append(pos, hash)

	// Go through the proofHashes and look for siblings of the newly hashed parent.
	// If we find the sibling, we'll hash with the sibling to get the parent until we
	// no longer find siblings.
	idx := slices.IndexFunc(proofHashes.positions, func(elem uint64) bool { return elem == sibling(pos) })
	for idx != -1 {
		// Calculate the parent hash and the position.
		if isLeftNiece(pos) {
			hash = parentHash(hash, proofHashes.hashes[idx])
		} else {
			hash = parentHash(proofHashes.hashes[idx], hash)
		}
		pos = parent(pos, forestRows)

		// Pop off the last appended proofHash and the sibling since
		// we hashed up.
		proofHashes.Delete(proofHashes.Len() - 1)
		proofHashes.Delete(idx)

		// Append the newly created parent.
		proofHashes.Append(pos, hash)

		// Look for the sibling of the newly created parent.
		idx = slices.IndexFunc(proofHashes.positions, func(elem uint64) bool { return elem == sibling(pos) })
	}

	return proofHashes
}

// RemoveTargets removes the selected targets from the given proof.
// NOTE The passed in proof MUST be a valid proof. There are no checks done so it is the caller's
// responsibility to make sure that the proof is valid.
func RemoveTargets(numLeaves uint64, delHashes []Hash, proof Proof, remTargets []uint64) ([]Hash, Proof) {
	forestRows := treeRows(numLeaves)

	// Copy targets to avoid mutating the original.
	targets := make([]uint64, len(proof.Targets))
	copy(targets, proof.Targets)
	targetHashesWithPos := toHashAndPos(targets, delHashes)

	// Calculate the positions of the proofs that we currently have.
	sort.Slice(targets, func(a, b int) bool { return targets[a] < targets[b] })
	havePositions, _ := proofPositions(targets, numLeaves, forestRows)
	proofHashesWithPos := toHashAndPos(havePositions, proof.Proof)

	// Merge the target hashes and proof hashes and sort. We do this as some targets may become
	// a proof.
	proofHashesWithPos = mergeSortedHashAndPos(proofHashesWithPos, targetHashesWithPos)

	// Remove the remTargets from the targets.
	targetHashesWithPos = subtractSortedHashAndPos(targetHashesWithPos, remTargets, uint64Cmp)

	// Extract hashes and positions.
	targetHashes := targetHashesWithPos.hashes
	targets = targetHashesWithPos.positions

	// Get rid of all the leftover targets from the proofs.
	proofHashesWithPos = subtractSortedHashAndPos(proofHashesWithPos, targets, uint64Cmp)

	// Calculate all the subtrees that we're interested in. We'll use this to leave out positions
	// that are not included in the subtrees here.
	//
	// Example: If we're only interested in subtree 0 (positions 00, 01, 02, 03), we'll leave
	// out position 04 and 05.
	//
	// 12
	// |-------\
	// 08      09      10
	// |---\   |---\   |---\
	// 00  01  02  03  04  05  06
	subTrees := []uint8{}
	for _, target := range targets {
		subTree, _, _, _ := detectOffset(target, numLeaves)

		idx := slices.Index(subTrees, subTree)
		if idx == -1 {
			subTrees = append(subTrees, subTree)
		}
	}

	// Take out proofs that are not in the subtrees our new targets are located in.
	for i := 0; i < proofHashesWithPos.Len(); i++ {
		proof := proofHashesWithPos.positions[i]
		subTree, _, _, _ := detectOffset(proof, numLeaves)

		if !slices.Contains(subTrees, subTree) {
			idx := slices.IndexFunc(proofHashesWithPos.positions, func(elem uint64) bool { return elem == proof })
			proofHashesWithPos.Delete(idx)
			i--
		}
	}

	// These are the positions that we need to calculate the new targets after deletion.
	wantPositions, calculateable := proofPositions(targets, numLeaves, forestRows)
	wantPositions = mergeSortedSlicesFunc(wantPositions, calculateable, uint64Cmp)

	// These are all the positions that want to get rid of.
	removePositions, _ := proofPositions(remTargets, numLeaves, forestRows)
	removePositions = mergeSortedSlicesFunc(removePositions, remTargets, uint64Cmp)

	// There are some positions we want that are included in the removePositions. Subtract those
	// from removePositions because we need them.
	removePositions = subtractSortedSlice(removePositions, wantPositions, uint64Cmp)

	// Go through all the removePositions from the proof, hashing up as needed.
	proofIdx := 0
	for i := 0; i < len(removePositions); i++ {
		if proofIdx >= len(proofHashesWithPos.positions) {
			break
		}

		proofPos := proofHashesWithPos.positions[proofIdx]
		proofHash := proofHashesWithPos.hashes[proofIdx]
		removePosition := removePositions[i]

		if removePosition == proofPos {
			// The proofs are always sorted. Look at the next or the previous proof and check for sibling-ness.
			// Then we call hash siblings and hash up to get the required proof. This needs to be done because
			// the deleted proof may hash up to a required calculate-able proof.
			//
			// Example:
			// In this below tree, if the targets are [00, 04] and we're deleting 00, then we need to hash up to
			// 12 when deleting 00 as 12 is a required proof for 04.
			//
			// 14
			// |---------------\
			// 12              13
			// |-------\       |-------\
			// 08      09      10      11
			// |---\   |---\   |---\   |---\
			// 00  01  02  03  04  05  06  07
			if proofIdx < proofHashesWithPos.Len()-1 && proofHashesWithPos.positions[proofIdx+1] == rightSib(proofPos) {
				proofHashesWithPos = hashSiblings(proofHashesWithPos, proofPos, proofHash, proofHashesWithPos.hashes[proofIdx+1], forestRows)

				proofHashesWithPos.Delete(proofIdx)
				proofHashesWithPos.Delete(proofIdx)
			} else if proofIdx >= 1 && proofHashesWithPos.positions[proofIdx-1] == leftSib(proofPos) {
				proofHashesWithPos = hashSiblings(proofHashesWithPos, proofPos, proofHash, proofHashesWithPos.hashes[proofIdx-1], forestRows)

				proofHashesWithPos.Delete(proofIdx - 1)
				proofHashesWithPos.Delete(proofIdx - 1)
				proofIdx-- // decrement since we're taking out an element from the left side.
			} else {
				// If there are no siblings present, just remove it.
				proofHashesWithPos.Delete(proofIdx)
			}

			sort.Sort(proofHashesWithPos)
		} else if removePosition < proofPos {
			continue
		} else {
			proofIdx++
			i--
		}
	}

	sort.Sort(proofHashesWithPos)

	return targetHashes, Proof{targets, proofHashesWithPos.hashes}
}

// AddProof adds the newProof onto the existing proof and return the new cachedDelHashes and proof. Newly calculateable
// positions and duplicates are excluded in the returned proof.
func AddProof(proofA, proofB Proof, targetHashesA, targetHashesB []Hash, numLeaves uint64) ([]Hash, Proof) {
	totalRows := treeRows(numLeaves)

	// Calculate proof hashes for proof A and add positions to the proof hashes.
	targetsA := copySortedFunc(proofA.Targets, uint64Less)
	proofPosA, calculateableA := proofPositions(targetsA, numLeaves, totalRows)
	proofAndPosA := hashAndPos{proofPosA, proofA.Proof}

	// Calculate proof hashes for proof B and add positions to the proof hashes.
	targetsB := copySortedFunc(proofB.Targets, uint64Less)
	proofPosB, calculateableB := proofPositions(targetsB, numLeaves, totalRows)
	proofAndPosB := hashAndPos{proofPosB, proofB.Proof}

	// Add the proof hashes of proofA and proofB.
	proofAndPosC := mergeSortedHashAndPos(proofAndPosA, proofAndPosB)

	// All the calculateables are proofs that we'll get rid of as we don't need them.
	// In the below tree, a proof for only [02, 03] would be [04]. But if we add targets
	// [00, 01] to this proof, then we don't need [04] anymore since it's calculateable.
	//
	// 06
	// |-------\
	// 04      05
	// |---\   |---\
	// 00  01  02  03
	calculateableC := mergeSortedSlicesFunc(calculateableA, calculateableB, uint64Cmp)
	proofAndPosC = subtractSortedHashAndPos(proofAndPosC, calculateableC, uint64Cmp)

	// Subtract all the targets from the proof.
	//
	// For trees like the one below, a target may be a proof for another target.
	// With the below tree, 05 is a target but it's also a proof for 00 and 01.
	// If we have a proof where we have targets [00, 05], then 05 should not be
	// in the proof since we already have it.
	//
	// 06
	// |-------\
	// 04      05
	// |---\   |---\
	// 00  01
	targetsC := mergeSortedSlicesFunc(targetsA, targetsB, uint64Cmp)
	proofAndPosC = subtractSortedHashAndPos(proofAndPosC, targetsC, uint64Cmp)

	// Extract the proof hashes.
	retProof := Proof{targetsC, proofAndPosC.hashes}

	// Get the hashes for the targets.
	cachedDelHashAndPosA := toHashAndPos(proofA.Targets, targetHashesA)

	cachedDelHashAndPosB := toHashAndPos(proofB.Targets, targetHashesB)
	cachedDelHashAndPosC := mergeSortedHashAndPos(cachedDelHashAndPosA, cachedDelHashAndPosB)

	return cachedDelHashAndPosC.hashes, retProof
}

// UpdateProofRemove modifies the cached proof with the deletions that happen in the block proof.
// It updates the necessary proof hashes and un-caches the targets that are being deleted.
func UpdateProofRemove(cachedProof, blockProof Proof, cachedDelHashes, blockDelHashes []Hash, numLeaves uint64) ([]Hash, Proof) {
	// First we calculate which hashes are going to be deleted from the cached hashes.
	// The resulting desiredHashesWithPos are the hashes that we will be caching after
	// the deletion.
	desiredHashesWithPos := toHashAndPos(cachedProof.Targets, cachedDelHashes)
	blockHashesWithPos := toHashAndPos(blockProof.Targets, blockDelHashes)
	desiredHashesWithPos = subtractSortedHashAndPos(desiredHashesWithPos, blockHashesWithPos.positions, uint64Cmp)

	// Combine the proofs so we have all the data that we need.
	combinedDelHashes, combinedProof := AddProof(cachedProof, blockProof, cachedDelHashes, blockDelHashes, numLeaves)
	// Calculate the proof after deleting the blockProof targets.
	combinedDelHashes, combinedProof = proofAfterPartialDeletion(numLeaves, combinedProof, combinedDelHashes, blockProof.Targets)
	// Then remove the blockProof targets as these need to be uncached.
	// This removal process also calculates the proof hashes.
	blockDelHashes, blockProof = proofAfterDeletion(numLeaves, blockProof)

	// Calculate the positions that should be removed from the combined proof by removing
	// the desired hashes from the block deletion hashes.

	blockDelHashesWithPos := toHashAndPos(blockProof.Targets, blockDelHashes)
	blockDelHashesWithPos = removeHashesFromHashAndPos(blockDelHashesWithPos, desiredHashesWithPos.hashes, func(elem Hash) Hash { return elem })
	removeTargets := make([]uint64, blockDelHashesWithPos.Len())
	copy(removeTargets, blockDelHashesWithPos.positions)

	// Remove the unnecessary positions from the combined proof.
	combinedDelHashes, combinedProof = RemoveTargets(numLeaves, combinedDelHashes, combinedProof, removeTargets)

	return combinedDelHashes, combinedProof
}

// UpdateProofAdd modifies the cached proof with the additions that are passed in.
// It adds the necessary proof hashes that will be needed to prove the targets in
// the cached proof.
//
// NOTE: the stump passed in to the UpdateProofAdd is assumed to already be modified
// with the deletion.
func UpdateProofAdd(cachedProof Proof, cachedHashes, adds []Hash, remembers []uint32, stump Stump) ([]Hash, Proof) {
	// Update target positions if the forest has remapped to a higher row.
	newForestRows := treeRows(stump.NumLeaves + uint64(len(adds)))
	oldForestRows := treeRows(stump.NumLeaves)
	if newForestRows > oldForestRows {
		for i, target := range cachedProof.Targets {
			row := detectRow(target, treeRows(stump.NumLeaves))

			oldStartPos := startPositionAtRow(row, oldForestRows)
			newStartPos := startPositionAtRow(row, newForestRows)

			offset := target - oldStartPos

			cachedProof.Targets[i] = offset + newStartPos
		}
	}

	cachedHashes, cachedProof, newRootsMap := getNewPositionsAfterAdd(
		cachedProof, cachedHashes, adds, remembers, stump, newForestRows)
	stump.NumLeaves += uint64(len(adds))

	// These are the positions that we'd need after the addition.
	cachedProofTargets := copySortedFunc(cachedProof.Targets, uint64Less)
	neededProofPositions, _ := proofPositions(cachedProofTargets, stump.NumLeaves, newForestRows)

	proofHashes := make([]Hash, len(neededProofPositions))
	for i, neededProofPosition := range neededProofPositions {
		hash := newRootsMap[neededProofPosition]
		proofHashes[i] = hash
	}

	cachedProof.Proof = proofHashes

	return cachedHashes, cachedProof
}

// getNewPositionsAfterAdd returns updated proof positions and the newly created
// positions in the map.
func getNewPositionsAfterAdd(cachedProof Proof, cachedHashes, adds []Hash,
	remembers []uint32, stump Stump, forestRows uint8) ([]Hash, Proof, map[uint64]Hash) {

	// Create a map of all the proof positions and their hashes. We'll use this
	// map to fetch the needed proof positions after the addition.
	proofPos, _ := proofPositions(cachedProof.Targets, stump.NumLeaves, forestRows)
	newRootsMap := make(map[uint64]Hash)
	for i, pos := range proofPos {
		newRootsMap[pos] = cachedProof.Proof[i]
	}

	cachedTargetsWithHash := toHashAndPos(cachedProof.Targets, cachedHashes)

	remembersIdx := 0
	roots := stump.Roots
	for i, add := range adds {
		if len(remembers) > 0 && remembersIdx < len(remembers) &&
			remembers[remembersIdx] == uint32(i) {

			cachedTargetsWithHash = mergeSortedHashAndPos(cachedTargetsWithHash,
				hashAndPos{[]uint64{stump.NumLeaves}, []Hash{add}})
			remembersIdx++
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
		for h := uint8(0); (stump.NumLeaves>>h)&1 == 1; h++ {
			root := roots[len(roots)-1]
			roots = roots[:len(roots)-1]

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
				pos := rootPosition(stump.NumLeaves, h, forestRows)

				sib := sibling(pos)
				cachedTargetsWithHash.positions = updatePositions(cachedTargetsWithHash.positions, sib, forestRows,
					func(e uint64) uint64 { return e },
					func(i int, pos uint64) { cachedTargetsWithHash.positions[i] = pos })

				tmpMap := make(map[uint64]Hash)
				for key, hash := range newRootsMap {
					ancestor := isAncestor(parent(sib, forestRows), key, forestRows)
					if ancestor {
						// We can ignore the error since we've already verified that
						// the proofAndPos[j] is an ancestor of sib.
						nextPos, _ := calcNextPosition(key, sib, forestRows)
						tmpMap[nextPos] = hash
					} else {
						tmpMap[key] = hash
					}
				}
				newRootsMap = tmpMap

				continue
			} else {
				pos := rootPosition(stump.NumLeaves, h, forestRows)

				// Check if positions will be updated and update
				// if they will be.
				if _, found := newRootsMap[pos]; !found {
					newRootsMap[pos] = root
				}
				if _, found := newRootsMap[pos^1]; !found {
					newRootsMap[pos^1] = newRoot
				}

				// Calculate the hash of the new root and append it.
				newRoot = parentHash(root, newRoot)
				pos = parent(pos, forestRows)

				if _, found := newRootsMap[pos]; !found {
					newRootsMap[pos] = newRoot
				}
			}
		}
		roots = append(roots, newRoot)
		stump.NumLeaves++
	}

	cachedProof.Targets = cachedTargetsWithHash.positions
	return cachedTargetsWithHash.hashes, cachedProof, newRootsMap
}

// rootsAfterDel returns the roots after the deletion in the blockProof has happened.
// NOTE: This function does not verify the proof. That responsibility is on the caller.
func rootsAfterDel(blockProof Proof, stump Stump) ([]Hash, error) {
	// Calculate all the current root positions.
	rootPositions := []uint64{}
	for _, root := range stump.Roots {
		pos := whichRoot(stump.NumLeaves, root, stump.Roots)
		rootPositions = append(rootPositions, pos)
	}

	rootCandidates := calculateRoots(stump.NumLeaves, nil, blockProof)

	// Calculate the roots that will be calculated from the proof.
	calcRootPositions := []uint64{}
	for _, del := range blockProof.Targets {
		root, err := getRootPosition(del, stump.NumLeaves, treeRows(stump.NumLeaves))
		if err != nil {
			return nil, err
		}
		calcRootPositions = mergeSortedSlicesFunc(calcRootPositions, []uint64{root}, uint64Cmp)
	}

	// Look for the positions that match up and replace the hash with the newly
	// calculated hash.
	idx := 0
	for i := len(rootPositions) - 1; i >= 0; i-- {
		rootPosition := rootPositions[i]

		if idx < len(rootCandidates) && rootPosition == calcRootPositions[idx] {
			stump.Roots[i] = rootCandidates[idx]
			idx++
		}
	}

	return stump.Roots, nil
}

// UpdateProof updates the cachedProof with the given blockProof and adds.
func UpdateProof(cachedProof, blockProof Proof, cachedDelHashes, blockDelHashes,
	adds []Hash, remembers []uint32, stump Stump) ([]Hash, Proof, error) {

	// Remove necessary targets and update proof hashes with the blockProof.
	cachedDelHashes, cachedProof = UpdateProofRemove(cachedProof, blockProof,
		cachedDelHashes, blockDelHashes, stump.NumLeaves)

	// Modify the roots with the blockProof.
	var err error
	stump.Roots, err = rootsAfterDel(blockProof, stump)
	if err != nil {
		return nil, Proof{}, err
	}

	// Add new proof hashes as needed.
	cachedDelHashes, cachedProof = UpdateProofAdd(cachedProof, cachedDelHashes, adds, remembers, stump)

	return cachedDelHashes, cachedProof, nil
}

// GetProofSubset trims away the un-needed data from the proof and returns a proof only
// for the passed in removes. An error is returned if the passed in proof does not have
// all the targets in the removes.
func GetProofSubset(proof Proof, hashes []Hash, removes []uint64, numLeaves uint64) ([]Hash, Proof, error) {
	// Copy to avoid mutating the original.
	proofTargetsCopy := copySortedFunc(proof.Targets, uint64Less)

	// Check that all the targets in removes are also present in the proof.
	expectedEmpty := copySortedFunc(removes, uint64Less)
	expectedEmpty = subtractSortedSlice(expectedEmpty, proofTargetsCopy, uint64Cmp)
	if len(expectedEmpty) > 0 {
		err := fmt.Errorf("Missing positions %v from the proof. Deletions %v, proof.Targets %v",
			expectedEmpty, removes, proof.Targets)
		return nil, Proof{}, err
	}

	// Create a copy of the proof that we'll mutate and return.
	retProof := Proof{
		make([]uint64, len(proof.Targets)),
		make([]Hash, len(proof.Proof)),
	}
	copy(retProof.Targets, proof.Targets)
	copy(retProof.Proof, proof.Proof)

	// These are all the targets that we'll remove so that the returned proof will only
	// prove the removes passed in.
	sort.Slice(removes, func(a, b int) bool { return removes[a] < removes[b] })
	proofTargetsCopy = subtractSortedSlice(proofTargetsCopy, removes, uint64Cmp)

	// Remove the targets and return the results.
	retHashes, retProof := RemoveTargets(numLeaves, hashes, retProof, proofTargetsCopy)
	return retHashes, retProof, nil
}
