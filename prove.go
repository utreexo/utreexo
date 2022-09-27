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

// getHashAndPosHashSubset allocates and returns a new hashAndPos that is the
// intersection of a and b based on the hashes in b.
func getHashAndPosHashSubset(a hashAndPos, b []Hash) hashAndPos {
	allKeys := make(map[Hash]bool, len(b))
	for _, elem := range b {
		allKeys[elem] = true
	}

	c := hashAndPos{make([]uint64, 0, len(b)), make([]Hash, 0, len(b))}
	for i := 0; i < a.Len(); i++ {
		elem := a.hashes[i]

		if _, val := allKeys[elem]; val {
			c.Append(a.positions[i], a.hashes[i])
		}
	}

	return c
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

	_, rootCandidates := calculateHashes(p.NumLeaves, delHashes, proof)
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

// getNextHash returns the hash of the parent of these two hashes.
func getNextHash(pos uint64, hash, sibHash Hash) Hash {
	// There's 3 different outcomes:
	// 1: Current hash is empty -> move the sibling up.
	// 2: Sibling hash is empty -> move the current hash up.
	// 3: Both are not empty -> hash them.
	var nextHash Hash
	if hash == empty {
		nextHash = sibHash
	} else if sibHash == empty {
		nextHash = hash
	} else {
		if isLeftNiece(pos) {
			nextHash = parentHash(hash, sibHash)
		} else {
			nextHash = parentHash(sibHash, hash)
		}
	}

	return nextHash
}

// nextLeastSlice returns the index of the slice that's has the lesser position
// in the given indexes. Returns -1 if the length of both slices are less than
// their indexes.
func nextLeastSlice(slice1, slice2 []uint64, idx1, idx2 int) int {
	if len(slice1) > idx1 && len(slice2) > idx2 {
		if slice1[idx1] < slice2[idx2] {
			return 0
		} else {
			return 1
		}
	} else if len(slice1) > idx1 && len(slice2) <= idx2 {
		return 0
	} else if len(slice1) <= idx1 && len(slice2) > idx2 {
		return 1
	}

	return -1
}

// getNextPos returns the next position in the given slices along with
// index of the slice and the index of the sibling slice (if there's a sibling).
func getNextPos(slice1, slice2 []uint64, slice1Idx, slice2Idx int) (uint64, int, int) {
	// Grab the next position.
	var pos uint64
	idx := nextLeastSlice(slice1, slice2, slice1Idx, slice2Idx)
	if idx == 0 {
		pos = slice1[slice1Idx]
		slice1Idx++
	} else if idx == 1 {
		pos = slice2[slice2Idx]
		slice2Idx++
	} else {
		// Break if we don't have anymore elements left.
		return pos, -1, -1
	}

	// Attempt to grab the sibling of the current position to process.
	sibIdx := nextLeastSlice(slice1, slice2, slice1Idx, slice2Idx)
	if sibIdx == 0 {
		if rightSib(pos) != slice1[slice1Idx] {
			sibIdx = -1
		}
	} else if sibIdx == 1 {
		if rightSib(pos) != slice2[slice2Idx] {
			sibIdx = -1
		}
	}

	return pos, idx, sibIdx
}

// calculateHashes returns the hashes of the roots and all the nodes that
// were used to calculate the roots. Passing nil delHashes will return the
// hashes of the roots and the nodes used to calculate the roots after the
// deletion of the targets.
func calculateHashes(numLeaves uint64, delHashes []Hash, proof Proof) (hashAndPos, []Hash) {
	totalRows := treeRows(numLeaves)

	// Where all the parent hashes we've calculated in a given row will go to.
	nextProves := hashAndPos{make([]uint64, 0, len(proof.Targets)), make([]Hash, 0, len(proof.Targets))}
	nextProvesIdx := 0

	// These are the leaves to be proven. Each represent a position and the
	// hash of a leaf.
	if delHashes == nil {
		delHashes = make([]Hash, len(proof.Targets))
	}
	toProve := toHashAndPos(proof.Targets, delHashes)
	toProveIdx := 0

	// Where all the root hashes that we've calculated will go to.
	calculatedRootHashes := make([]Hash, 0, numRoots(numLeaves))

	// Separate index for the hashes in the passed in proof.
	proofHashIdx := 0
	for row := uint8(0); row <= totalRows; {
		// Grab the next position and hash to process.
		var proveHash Hash
		provePos, idx, sibIdx := getNextPos(toProve.positions, nextProves.positions, toProveIdx, nextProvesIdx)
		if idx == -1 {
			break
		}
		if idx == 0 {
			proveHash = toProve.hashes[toProveIdx]
			toProveIdx++
		} else {
			proveHash = nextProves.hashes[nextProvesIdx]
			nextProvesIdx++
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

		var sibHash Hash
		sibPresent := sibIdx != -1
		if sibPresent {
			if sibIdx == 0 {
				sibHash = toProve.hashes[toProveIdx]
				toProveIdx++
			} else {
				sibHash = nextProves.hashes[nextProvesIdx]
				nextProvesIdx++
			}
		} else {
			// If the next prove isn't the sibling of this prove, we fetch
			// the next proof hash to calculate the parent.
			sibHash = proof.Proof[proofHashIdx]
			proofHashIdx++
		}

		// Calculate the next hash.
		nextHash := getNextHash(provePos, proveHash, sibHash)
		nextProves.Append(parent(provePos, totalRows), nextHash)
	}

	// Add in the targets as well since we need them as well to calculate up
	// to the roots.
	nextProves = mergeSortedHashAndPos(nextProves, toProve)
	return nextProves, calculatedRootHashes
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

// getNewPositions updates all the positions in the slice after the blockTargets have been deleted.
func getNewPositions(blockTargets []uint64, slice hashAndPos, numLeaves uint64, appendRoots bool) hashAndPos {
	totalRows := treeRows(numLeaves)
	newSlice := hashAndPos{make([]uint64, 0, slice.Len()), make([]Hash, 0, slice.Len())}

	row := uint8(0)
	for i, pos := range slice.positions {
		hash := slice.hashes[i]
		if hash == empty {
			continue
		}

		for pos > maxPossiblePosAtRow(row, totalRows) && row <= totalRows {
			row++
		}
		if row > totalRows {
			break
		}

		nextPos := pos
		for _, target := range blockTargets {
			if isRootPositionOnRow(nextPos, numLeaves, row, totalRows) {
				break
			}

			// If these positions are in different subtrees, continue.
			subtree, _, _, _ := detectOffset(target, numLeaves)
			subtree1, _, _, _ := detectOffset(nextPos, numLeaves)
			if subtree != subtree1 {
				continue
			}

			if isAncestor(parent(target, totalRows), nextPos, totalRows) {
				nextPos, _ = calcNextPosition(nextPos, target, totalRows)
			}
		}

		if appendRoots {
			newSlice.Append(nextPos, hash)
		} else {
			if !isRootPositionOnRow(nextPos, numLeaves, row, totalRows) {
				newSlice.Append(nextPos, hash)
			}
		}
	}

	sort.Sort(newSlice)

	return newSlice
}

// updateProofRemove modifies the cached proof with the deletions that happen in the block proof.
// It updates the necessary proof hashes and un-caches the targets that are being deleted.
func (p *Proof) updateProofRemove(blockTargets []uint64, cachedHashes []Hash, updated hashAndPos, numLeaves uint64) []Hash {
	totalRows := treeRows(numLeaves)

	// Delete from the target.
	sortedBlockTargets := copySortedFunc(blockTargets, uint64Less)
	targetsWithHash := toHashAndPos(p.Targets, cachedHashes)
	targetsWithHash = subtractSortedHashAndPos(targetsWithHash, sortedBlockTargets, uint64Cmp)

	// Attach positions to the proofs.
	sortedCachedTargets := copySortedFunc(p.Targets, uint64Less)
	proofPos, _ := proofPositions(sortedCachedTargets, numLeaves, totalRows)
	oldProofs := toHashAndPos(proofPos, p.Proof)
	newProofs := hashAndPos{make([]uint64, 0, len(p.Proof)), make([]Hash, 0, len(p.Proof))}

	// Grab all the positions of the needed proof hashes.
	neededPos, _ := proofPositions(targetsWithHash.positions, numLeaves, totalRows)

	// Grab the un-needed positions. These are un-needed as they were proofs
	// for the now deleted targets.
	extraPos := copySortedFunc(oldProofs.positions, uint64Less)
	extraPos = subtractSortedSlice(extraPos, neededPos, uint64Cmp)

	// Loop through oldProofs and only add the needed proof hashes.
	idx, extraIdx := 0, 0
	for i, pos := range oldProofs.positions {
		for extraIdx < len(extraPos) && extraPos[extraIdx] < pos {
			extraIdx++
		}
		if extraIdx < len(extraPos) && extraPos[extraIdx] == pos {
			continue
		}

		for idx < updated.Len() && updated.positions[idx] < pos {
			idx++
		}
		if idx < updated.Len() && updated.positions[idx] == pos {
			if updated.hashes[idx] != empty {
				newProofs.Append(pos, updated.hashes[idx])
			}
		} else {
			newProofs.Append(pos, oldProofs.hashes[i])
		}
	}

	// Missing positions are the newly needed positions that aren't present in the proof.
	// These positions are there because they were calculateable before the deletion in the
	// previous proof.
	missingPos := copySortedFunc(neededPos, uint64Less)
	missingPos = subtractSortedSlice(missingPos, oldProofs.positions, uint64Cmp)
	missingPos = subtractSortedSlice(missingPos, sortedBlockTargets, uint64Cmp)

	// Loop through the missingPos and add missing positions.
	idx = 0
	for _, missing := range missingPos {
		for idx < updated.Len() && updated.positions[idx] < missing {
			idx++
		}

		if idx < updated.Len() && updated.positions[idx] == missing {
			newProofs.Append(missing, updated.hashes[idx])
		}
	}

	// Update positions.
	sortedBlockTargets = deTwin(sortedBlockTargets, totalRows)
	targetsWithHash = getNewPositions(sortedBlockTargets, targetsWithHash, numLeaves, true)
	newProofs = getNewPositions(sortedBlockTargets, newProofs, numLeaves, false)

	*p = Proof{targetsWithHash.positions, newProofs.hashes}
	return targetsWithHash.hashes
}

// Update updates the proof with the given data.
func (p *Proof) Update(
	cachedHashes, addHashes []Hash, blockTargets []uint64, remembers []uint32, updateData UpdateData) ([]Hash, error) {

	// Remove necessary targets and update proof hashes with the blockProof.
	cachedHashes = p.updateProofRemove(
		blockTargets, cachedHashes, hashAndPos{updateData.NewDelPos, updateData.NewDelHash},
		updateData.PrevNumLeaves)

	cachedHashes = p.updateProofAdd(addHashes, cachedHashes, remembers,
		hashAndPos{updateData.NewAddPos, updateData.NewAddHash},
		updateData.PrevNumLeaves, updateData.ToDestroy)

	return cachedHashes, nil
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

// maybeRemap remaps the passed in hash and pos if the treeRows increase after
// adding the new nodes.
func maybeRemap(numLeaves, numAdds uint64, hnp hashAndPos) hashAndPos {
	// Update target positions if the forest has remapped to a higher row.
	newForestRows := treeRows(numLeaves + numAdds)
	oldForestRows := treeRows(numLeaves)
	if newForestRows > oldForestRows {
		for i, pos := range hnp.positions {
			row := detectRow(pos, treeRows(numLeaves))

			oldStartPos := startPositionAtRow(row, oldForestRows)
			newStartPos := startPositionAtRow(row, newForestRows)

			offset := pos - oldStartPos

			hnp.positions[i] = offset + newStartPos
		}
	}

	return hnp
}

// updateProofAdd modifies the cached proof with the additions that are passed in.
// It adds the necessary proof hashes that will be needed to prove the targets in
// the cached proof and updates the positions of the cached targets as needed.
func (p *Proof) updateProofAdd(adds, cachedDelHashes []Hash, remembers []uint32,
	newNodes hashAndPos, beforeNumLeaves uint64, toDestroy []uint64) []Hash {

	// Combine the hashes with the targets.
	origTargetsWithHash := toHashAndPos(p.Targets, cachedDelHashes)

	// Attach positions to the proof.
	proofPos, _ := proofPositions(origTargetsWithHash.positions, beforeNumLeaves, treeRows(beforeNumLeaves))
	proofWithPos := toHashAndPos(proofPos, p.Proof)

	// Remap the positions if we moved up a after the addition row.
	origTargetsWithHash = maybeRemap(beforeNumLeaves, uint64(len(adds)), origTargetsWithHash)
	proofWithPos = maybeRemap(beforeNumLeaves, uint64(len(adds)), proofWithPos)

	// Move up positions that need to be moved up due to the empty roots
	// being written over.
	for _, del := range toDestroy {
		origTargetsWithHash = getNewPositions([]uint64{del}, origTargetsWithHash, beforeNumLeaves+uint64(len(adds)), true)
		proofWithPos = getNewPositions([]uint64{del}, proofWithPos, beforeNumLeaves+uint64(len(adds)), true)
	}

	// Add in proofHashes to the newNodes as some needed hashes
	// will be in the proof hashes.
	newNodes = mergeSortedHashAndPos(newNodes, proofWithPos)

	// Grab all the new hashes to be cached.
	remembersIdx := 0
	addHashes := []Hash{}
	for i := 0; i < len(adds); i++ {
		add := adds[i]
		if remembersIdx >= len(remembers) {
			break
		}

		if uint32(i) == remembers[remembersIdx] {
			addHashes = append(addHashes, add)
			remembersIdx++
		} else if uint32(i) > remembers[remembersIdx] {
			remembersIdx++
			i--
		}
	}
	remembersWithHash := getHashAndPosHashSubset(newNodes, addHashes)

	// Add the new hashes to be cached to the current hashes.
	origTargetsWithHash = mergeSortedHashAndPos(remembersWithHash, origTargetsWithHash)

	// Grab all the new nodes after this add.
	neededProofPositions, _ := proofPositions(origTargetsWithHash.positions, beforeNumLeaves+uint64(len(adds)), treeRows(beforeNumLeaves+uint64(len(adds))))

	// Add all the new proof hashes to the proof.
	newProofWithPos := hashAndPos{}
	newNodesIdx := 0
	for _, pos := range neededProofPositions {
		for newNodesIdx < newNodes.Len() && newNodes.positions[newNodesIdx] < pos {
			newNodesIdx++
		}
		if newNodesIdx < newNodes.Len() && newNodes.positions[newNodesIdx] == pos {
			newProofWithPos.Append(newNodes.positions[newNodesIdx], newNodes.hashes[newNodesIdx])
		}
	}

	sort.Sort(newProofWithPos)
	p.Proof = newProofWithPos.hashes

	p.Targets = origTargetsWithHash.positions
	return origTargetsWithHash.hashes
}
