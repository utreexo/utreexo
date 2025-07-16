package utreexo

import (
	"encoding/hex"
	"fmt"
	"sort"
	"strings"

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
	proofPositions, _ := ProofPositions(sortedTargets, p.NumLeaves, TreeRows(p.NumLeaves))
	if len(proofPositions) == 0 {
		// Return early.
		return proof, nil
	}

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

// getHashAndPosSubset allocates and returns a new hashAndPos that is the
// intersection of a and b.
//
// NOTE: Both inputs MUST be sorted.
func getHashAndPosSubset(a hashAndPos, b []uint64) hashAndPos {
	c := hashAndPos{make([]uint64, 0, len(b)), make([]Hash, 0, len(b))}

	bIdx := 0
	for i := 0; i < a.Len(); i++ {
		if bIdx >= len(b) {
			break
		}
		// If they're equal, append element to c.
		if a.positions[i] == b[bIdx] {
			c.Append(a.positions[i], a.hashes[i])
			// Move both indexes forward if they're the same.
			bIdx++
		} else if a.positions[i] > b[bIdx] {
			bIdx++
			i--
		}
	}

	return c
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

func deTwinHashAndPos(hnp hashAndPos, forestRows uint8) hashAndPos {
	for i := 0; i < hnp.Len(); i++ {
		// 1: Check that there's at least 2 elements in the slice left.
		// 2: Check if the right sibling of the current element matches
		//    up with the next element in the slice.
		if i+1 < hnp.Len() && rightSib(hnp.positions[i]) == hnp.positions[i+1] {
			// Grab the position of the del.
			nodePos, nodeHash := hnp.positions[i], hnp.hashes[i]
			sibHash := hnp.hashes[i+1]

			// Remove both of the detwined nodes from the slice.
			hnp.Delete(i)
			hnp.Delete(i)

			// Calculate and insert the parent in order.
			position := Parent(nodePos, forestRows)
			hnp = mergeSortedHashAndPos(
				hnp,
				hashAndPos{[]uint64{position}, []Hash{parentHash(nodeHash, sibHash)}},
			)

			// Decrement one since the next element we should
			// look at is at the same index because the slice decreased
			// in length by one.
			i--
		}
	}

	return hnp
}

// Verify calculates the root hashes from the passed in proof and delHashes and
// compares it against the current roots in the pollard.
func (p *Pollard) Verify(delHashes []Hash, proof Proof, remember bool) error {
	if len(delHashes) == 0 {
		return nil
	}

	if len(delHashes) != len(proof.Targets) {
		return fmt.Errorf("Pollard.Verify fail. Was given %d targets but got %d hashes",
			len(proof.Targets), len(delHashes))
	}

	_, rootCandidates, err := calculateHashes(p.NumLeaves, delHashes, proof)
	if err != nil {
		return err
	}
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

type insertDelInfo struct {
	pHash    Hash
	sibHash  Hash
	prevHash Hash
	isLeft   bool
}

type updateHashInfo struct {
	curHash  Hash
	origHash Hash
	isRoot   bool
	rootPos  uint64
}

type UndoInfo struct {
	insertDelInfos  []*insertDelInfo
	updateHashInfos []*updateHashInfo
}

func (u *UndoInfo) addUpdateHashInfo(info updateHashInfo) {
	u.updateHashInfos = append(u.updateHashInfos, &info)
	u.insertDelInfos = append(u.insertDelInfos, nil)
}

func (u *UndoInfo) addInsertDelInfo(info insertDelInfo) {
	u.insertDelInfos = append(u.insertDelInfos, &info)
	u.updateHashInfos = append(u.updateHashInfos, nil)
}

func (u *UndoInfo) pop() (*updateHashInfo, *insertDelInfo) {
	var uhInfo *updateHashInfo
	var idInfo *insertDelInfo

	uhInfo, u.updateHashInfos = u.updateHashInfos[len(u.updateHashInfos)-1], u.updateHashInfos[:len(u.updateHashInfos)-1]
	idInfo, u.insertDelInfos = u.insertDelInfos[len(u.insertDelInfos)-1], u.insertDelInfos[:len(u.insertDelInfos)-1]
	return uhInfo, idInfo
}

func (u *UndoInfo) length() int {
	return len(u.insertDelInfos)
}

func (u *UndoInfo) String() string {
	str := ""
	for i, uhInfo := range u.updateHashInfos {
		if uhInfo != nil {
			str += fmt.Sprintf("%v -> %v\n", uhInfo.origHash, uhInfo.curHash)
		} else {
			idInfo := u.insertDelInfos[i]
			str += fmt.Sprintf("%v(isLeft: %v), %v, %v\n",
				idInfo.prevHash, idInfo.isLeft, idInfo.sibHash, idInfo.pHash)
		}
	}

	return str
}

func initUndoInfo(count int) UndoInfo {
	u := UndoInfo{}
	u.insertDelInfos = make([]*insertDelInfo, 0, count)
	u.updateHashInfos = make([]*updateHashInfo, 0, count)

	return u
}

type IngestInstruction struct {
	Hashes []Hash
	isLeaf []bool
}

func (ins *IngestInstruction) String() string {
	str := ""
	for i, hash := range ins.Hashes {
		str += fmt.Sprintf("%v (%v)\n", hash, ins.isLeaf[i])
	}

	return str
}

type ModifyInstruction struct {
	Before    []Hash
	After     []Hash
	positions []uint64
}

func (m *ModifyInstruction) String() string {
	str := ""
	for i, beforeHash := range m.Before {
		str += fmt.Sprintf("(%v): %v -> %v\n", m.positions[i], beforeHash, m.After[i])
	}

	return str
}

func (m *ModifyInstruction) Detwin(totalRows uint8) {
	for i := 0; i < len(m.After); i++ {
		// 1: Check that there's at least 2 elements in the slice left.
		// 2: Check if the right sibling of the current element matches
		//    up with the next element in the slice.
		if i+1 < len(m.positions) && rightSib(m.positions[i]) == m.positions[i+1] {
			hash, sibHash := m.After[i], m.After[i+1]
			if hash != empty || sibHash != empty {
				continue
			}

			// Remove both of the detwined nodes from the slice.
			m.positions = append(m.positions[:i], m.positions[i+1:]...)
			m.Before = append(m.Before[:i], m.Before[i+1:]...)
			m.After = append(m.After[:i], m.After[i+1:]...)

			m.positions = append(m.positions[:i], m.positions[i+1:]...)
			m.Before = append(m.Before[:i], m.Before[i+1:]...)
			m.After = append(m.After[:i], m.After[i+1:]...)

			// Decrement one since the next element we should
			// look at is at the same index because the slice decreased
			// in length by one.
			i--
		}
	}
}

func (m *ModifyInstruction) RemoveParents(totalRows uint8) {
	for i := 0; i < len(m.After); i++ {
		hash, pos := m.After[i], m.positions[i]
		if hash != empty {
			continue
		}

		parent := Parent(pos, totalRows)

		idx := slices.Index(m.positions, parent)
		if idx == -1 {
			continue
		}

		// Remove both of the detwined nodes from the slice.
		m.positions = append(m.positions[:idx], m.positions[idx+1:]...)
		m.Before = append(m.Before[:idx], m.Before[idx+1:]...)
		m.After = append(m.After[:idx], m.After[idx+1:]...)

		// Decrement one since the next element we should
		// look at is at the same index because the slice decreased
		// in length by one.
		i--
	}
}

func calculateHashes3(numLeaves uint64, delHashes []Hash, proof Proof) (
	ModifyInstruction, UndoInfo, []Hash, error) {

	totalRows := TreeRows(numLeaves)

	// Where all the parent hashes we've calculated in a given row will go to.
	nextProves := hashAndPos{make([]uint64, 0, len(proof.Targets)), make([]Hash, 0, len(proof.Targets))}
	nextProvesIdx := 0

	// Where all the parent hashes we've calculated in a given row will go to.
	nextHashes := hashAndPos{make([]uint64, 0, len(proof.Targets)), make([]Hash, 0, len(proof.Targets))}

	undoInfo := initUndoInfo(len(proof.Proof))

	toProve := toHashAndPos(proof.Targets, delHashes)
	toProveIdx := 0

	// Where all the root hashes that we've calculated will go to.
	calculatedRootHashes := make([]Hash, 0, numRoots(numLeaves))

	// Separate index for the hashes in the passed in proof.
	proofHashIdx := 0
	for row := uint8(0); row <= totalRows; {
		// Grab the next position and hash to process.
		var proveHash Hash
		var modifyHash Hash
		provePos, idx, sibIdx := getNextPos(toProve.positions, nextProves.positions, toProveIdx, nextProvesIdx)
		if idx == -1 {
			break
		}
		if idx == 0 {
			proveHash = toProve.hashes[toProveIdx]
			modifyHash = empty
			toProveIdx++
		} else {
			proveHash = nextProves.hashes[nextProvesIdx]
			modifyHash = nextHashes.hashes[nextProvesIdx]
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
		if isRootPositionOnRow(provePos, numLeaves, row) {
			calculatedRootHashes = append(calculatedRootHashes, proveHash)

			//fmt.Println("next root", modifyHash, proveHash, provePos)
			if modifyHash == empty {
				undoInfo.addUpdateHashInfo(
					updateHashInfo{
						origHash: proveHash,
						curHash:  modifyHash,
						isRoot:   true,
						rootPos:  provePos,
					})
			}
			continue
		}

		var sibHash Hash
		var modifySibHash Hash
		sibPresent := sibIdx != -1
		if sibPresent {
			if sibIdx == 0 {
				sibHash = toProve.hashes[toProveIdx]
				modifySibHash = empty
				toProveIdx++
			} else {
				sibHash = nextProves.hashes[nextProvesIdx]
				modifySibHash = nextHashes.hashes[nextProvesIdx]
				nextProvesIdx++
			}
		} else {
			if len(proof.Proof) <= proofHashIdx {
				return ModifyInstruction{}, UndoInfo{}, nil,
					fmt.Errorf("invalid proof. Proof too short.")
			}

			// If the next prove isn't the sibling of this prove, we fetch
			// the next proof hash to calculate the parent.
			sibHash = proof.Proof[proofHashIdx]
			modifySibHash = sibHash
			proofHashIdx++
		}

		// Calculate the next hash.
		nextHash := getNextHash(provePos, proveHash, sibHash)
		nextProves.Append(Parent(provePos, totalRows), nextHash)

		modifyNextHash := getNextHash(provePos, modifyHash, modifySibHash)
		nextHashes.Append(Parent(provePos, totalRows), modifyNextHash)

		// Write undo info data.  If only one of the child is empty, this means its sibling
		// is moving up.
		if (modifyHash == empty) != (modifySibHash == empty) {
			if modifyHash == empty {
				undoInfo.addInsertDelInfo(
					insertDelInfo{
						pHash:    nextHash,
						sibHash:  modifySibHash,
						prevHash: proveHash,
						isLeft:   isLeftNiece(provePos),
					})
			} else {
				undoInfo.addInsertDelInfo(
					insertDelInfo{
						pHash:    nextHash,
						sibHash:  modifyHash,
						prevHash: sibHash,
						isLeft:   isLeftNiece(sibling(provePos)),
					})
			}
		} else if (modifyHash != empty) && (modifySibHash != empty) {
			// If neither are empty, then it's an existing node getting its hash updated.
			undoInfo.addUpdateHashInfo(
				updateHashInfo{
					origHash: nextHash,
					curHash:  modifyNextHash,
				})
		}
	}

	nextProves = mergeSortedHashAndPos(nextProves, toProve)
	for i := range toProve.hashes {
		toProve.hashes[i] = empty
	}
	nextHashes = mergeSortedHashAndPos(nextHashes, toProve)

	m := ModifyInstruction{
		Before:    nextProves.hashes,
		After:     nextHashes.hashes,
		positions: nextProves.positions,
	}

	return m, undoInfo, calculatedRootHashes, nil
}

func calculateHashes2(numLeaves uint64, delHashes []Hash, proof Proof) (
	IngestInstruction, ModifyInstruction, UndoInfo, []Hash, error) {

	totalRows := TreeRows(numLeaves)

	ingestIns := IngestInstruction{Hashes: make([]Hash, 0, len(delHashes)*2)}

	// Where all the parent hashes we've calculated in a given row will go to.
	nextProves := hashAndPos{make([]uint64, 0, len(proof.Targets)), make([]Hash, 0, len(proof.Targets))}
	nextProvesIdx := 0

	// Where all the parent hashes we've calculated in a given row will go to.
	nextHashes := hashAndPos{make([]uint64, 0, len(proof.Targets)), make([]Hash, 0, len(proof.Targets))}

	undoInfo := initUndoInfo(len(proof.Proof))

	toProve := toHashAndPos(proof.Targets, delHashes)
	toProveIdx := 0
	// Where all the root hashes that we've calculated will go to.
	calculatedRootHashes := make([]Hash, 0, numRoots(numLeaves))

	ingestInsParentToIndexMap := make(map[Hash]int, len(delHashes))

	// Separate index for the hashes in the passed in proof.
	proofHashIdx := 0
	for row := uint8(0); row <= totalRows; {
		// Grab the next position and hash to process.
		var proveHash Hash
		var modifyHash Hash
		provePos, idx, sibIdx := getNextPos(toProve.positions, nextProves.positions, toProveIdx, nextProvesIdx)
		if idx == -1 {
			break
		}
		if idx == 0 {
			proveHash = toProve.hashes[toProveIdx]
			modifyHash = empty
			toProveIdx++
		} else {
			proveHash = nextProves.hashes[nextProvesIdx]
			modifyHash = nextHashes.hashes[nextProvesIdx]
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
		if isRootPositionOnRow(provePos, numLeaves, row) {
			calculatedRootHashes = append(calculatedRootHashes, proveHash)

			//fmt.Println("next root", modifyHash, proveHash, provePos)
			if modifyHash == empty {
				undoInfo.addUpdateHashInfo(
					updateHashInfo{
						origHash: proveHash,
						curHash:  modifyHash,
						isRoot:   true,
						rootPos:  provePos,
					})
			}
			continue
		}

		var sibHash Hash
		var modifySibHash Hash
		sibPresent := sibIdx != -1
		if sibPresent {
			if sibIdx == 0 {
				sibHash = toProve.hashes[toProveIdx]
				modifySibHash = empty
				toProveIdx++
			} else {
				sibHash = nextProves.hashes[nextProvesIdx]
				modifySibHash = nextHashes.hashes[nextProvesIdx]
				nextProvesIdx++
			}
		} else {
			if len(proof.Proof) <= proofHashIdx {
				return IngestInstruction{}, ModifyInstruction{}, UndoInfo{}, nil,
					fmt.Errorf("invalid proof. Proof too short.")
			}

			// If the next prove isn't the sibling of this prove, we fetch
			// the next proof hash to calculate the parent.
			sibHash = proof.Proof[proofHashIdx]
			modifySibHash = sibHash
			proofHashIdx++
		}

		// Calculate the next hash.
		nextHash := getNextHash(provePos, proveHash, sibHash)
		nextProves.Append(Parent(provePos, totalRows), nextHash)

		insI, IFound := ingestInsParentToIndexMap[proveHash]
		insJ, JFound := ingestInsParentToIndexMap[sibHash]

		if IFound {
			ingestIns.Hashes[insI] = sibHash
			delete(ingestInsParentToIndexMap, proveHash)
		}
		if JFound {
			ingestIns.Hashes[insJ] = proveHash
			delete(ingestInsParentToIndexMap, sibHash)
		}

		// Add to the ingest instructions
		if isLeftNiece(provePos) {
			ingestIns.isLeaf = append(ingestIns.isLeaf, idx == 0, sibIdx == 0, false)
			ingestIns.Hashes = append(ingestIns.Hashes, proveHash, sibHash, nextHash)
			ingestInsParentToIndexMap[nextHash] = len(ingestIns.Hashes) - 1
		} else {
			ingestIns.isLeaf = append(ingestIns.isLeaf, sibIdx == 0, idx == 0, false)
			ingestIns.Hashes = append(ingestIns.Hashes, sibHash, proveHash, nextHash)
			ingestInsParentToIndexMap[nextHash] = len(ingestIns.Hashes) - 1
		}

		modifyNextHash := getNextHash(provePos, modifyHash, modifySibHash)
		nextHashes.Append(Parent(provePos, totalRows), modifyNextHash)

		// Write undo info data.  If only one of the child is empty, this means its sibling
		// is moving up.
		if (modifyHash == empty) != (modifySibHash == empty) {
			if modifyHash == empty {
				//fmt.Printf("0 removed %v, sib %v, parent %v\n", proveHash, modifySibHash, nextHash)

				undoInfo.addInsertDelInfo(
					insertDelInfo{
						pHash:    nextHash,
						sibHash:  modifySibHash,
						prevHash: proveHash,
						isLeft:   isLeftNiece(provePos),
					})
			} else {
				//fmt.Printf("1 removed %v, sib %v, parent %v\n", sibHash, modifyHash, nextHash)

				undoInfo.addInsertDelInfo(
					insertDelInfo{
						pHash:    nextHash,
						sibHash:  modifyHash,
						prevHash: sibHash,
						isLeft:   isLeftNiece(sibling(provePos)),
					})
			}
		} else if (modifyHash != empty) && (modifySibHash != empty) {
			// If neither are empty, then it's an existing node getting its hash updated.
			//fmt.Printf("%v -> %v\n", nextHash, modifyNextHash)

			undoInfo.addUpdateHashInfo(
				updateHashInfo{
					origHash: nextHash,
					curHash:  modifyNextHash,
				})
		}
	}

	nextProves = mergeSortedHashAndPos(nextProves, toProve)
	for i := range toProve.hashes {
		toProve.hashes[i] = empty
	}
	nextHashes = mergeSortedHashAndPos(nextHashes, toProve)

	m := ModifyInstruction{
		Before:    nextProves.hashes,
		After:     nextHashes.hashes,
		positions: nextProves.positions,
	}

	return ingestIns, m, undoInfo, calculatedRootHashes, nil
}

// calculateHashes returns the hashes of the roots and all the nodes that
// were used to calculate the roots. Passing nil delHashes will return the
// hashes of the roots and the nodes used to calculate the roots after the
// deletion of the targets.
func calculateHashes(numLeaves uint64, delHashes []Hash, proof Proof) (hashAndPos, []Hash, error) {
	totalRows := TreeRows(numLeaves)

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
		if isRootPositionOnRow(provePos, numLeaves, row) {
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
			if len(proof.Proof) <= proofHashIdx {
				return hashAndPos{}, nil, fmt.Errorf("invalid proof. Proof too short.")
			}

			// If the next prove isn't the sibling of this prove, we fetch
			// the next proof hash to calculate the parent.
			sibHash = proof.Proof[proofHashIdx]
			proofHashIdx++
		}

		// Calculate the next hash.
		nextHash := getNextHash(provePos, proveHash, sibHash)
		nextProves.Append(Parent(provePos, totalRows), nextHash)
	}

	// Add in the targets as well since we need them as well to calculate up
	// to the roots.
	nextProves = mergeSortedHashAndPos(nextProves, toProve)
	return nextProves, calculatedRootHashes, nil
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
	forestRows := TreeRows(numLeaves)

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
	desiredPositions, _ := ProofPositions(desiredTargets, numLeaves, forestRows)

	// havePositions represent all the positions in the tree we already have access to.
	// Since targets and computablePositions are something we already have, append
	// those to the havePositions.
	havePositions, computablePos := ProofPositions(targets, numLeaves, forestRows)
	havePositions = append(havePositions, targets...)
	havePositions = append(havePositions, computablePos...)
	sort.Slice(havePositions, func(a, b int) bool { return havePositions[a] < havePositions[b] })

	// Get rid of any positions that we already have.
	desiredPositions = subtractSortedSlice(desiredPositions, havePositions, uint64Cmp)

	return desiredPositions
}

// AddProof adds the newProof onto the existing proof and return the new cachedDelHashes and proof. Newly calculateable
// positions and duplicates are excluded in the returned proof.
func AddProof(proofA, proofB Proof, targetHashesA, targetHashesB []Hash, numLeaves uint64) ([]Hash, Proof) {
	totalRows := TreeRows(numLeaves)

	// Calculate proof hashes for proof A and add positions to the proof hashes.
	targetsA := copySortedFunc(proofA.Targets, uint64Cmp)
	proofPosA, calculateableA := ProofPositions(targetsA, numLeaves, totalRows)
	proofAndPosA := hashAndPos{proofPosA, proofA.Proof}

	// Calculate proof hashes for proof B and add positions to the proof hashes.
	targetsB := copySortedFunc(proofB.Targets, uint64Cmp)
	proofPosB, calculateableB := ProofPositions(targetsB, numLeaves, totalRows)
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
	totalRows := TreeRows(numLeaves)
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
			if isRootPositionOnRow(nextPos, numLeaves, row) {
				break
			}

			// If these positions are in different subtrees, continue.
			subtree, _, _, _ := DetectOffset(target, numLeaves)
			subtree1, _, _, _ := DetectOffset(nextPos, numLeaves)
			if subtree != subtree1 {
				continue
			}

			if isAncestor(Parent(target, totalRows), nextPos, totalRows) {
				nextPos, _ = calcNextPosition(nextPos, target, totalRows)
			}
		}

		if appendRoots {
			newSlice.Append(nextPos, hash)
		} else {
			if !isRootPositionOnRow(nextPos, numLeaves, row) {
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
	totalRows := TreeRows(numLeaves)

	// Delete from the target.
	sortedBlockTargets := copySortedFunc(blockTargets, uint64Cmp)
	targetsWithHash := toHashAndPos(p.Targets, cachedHashes)
	targetsWithHash = subtractSortedHashAndPos(targetsWithHash, sortedBlockTargets, uint64Cmp)

	// Attach positions to the proofs.
	sortedCachedTargets := copySortedFunc(p.Targets, uint64Cmp)
	proofPos, _ := ProofPositions(sortedCachedTargets, numLeaves, totalRows)
	oldProofs := toHashAndPos(proofPos, p.Proof)
	newProofs := hashAndPos{make([]uint64, 0, len(p.Proof)), make([]Hash, 0, len(p.Proof))}

	// Grab all the positions of the needed proof hashes.
	neededPos, _ := ProofPositions(targetsWithHash.positions, numLeaves, totalRows)

	// Grab the un-needed positions. These are un-needed as they were proofs
	// for the now deleted targets.
	extraPos := copySortedFunc(oldProofs.positions, uint64Cmp)
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
	missingPos := copySortedFunc(neededPos, uint64Cmp)
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

// Undo reverts the proof back to the previous state before the Update.
//
// NOTE Undo does NOT re-cache the already deleted leaves that were previously
// cached. Those must be added back to the cached proof separately.
func (p *Proof) Undo(numAdds, numLeaves uint64, dels []uint64,
	delHashes, cachedHashes []Hash, toDestroy []uint64, proof Proof) ([]Hash, error) {

	cachedHashes, err := p.undoAdd(numAdds, numLeaves, cachedHashes, toDestroy)
	if err != nil {
		return cachedHashes, err
	}

	cachedHashes, err = p.undoDel(dels, delHashes, cachedHashes, proof, numLeaves-numAdds)
	if err != nil {
		return cachedHashes, err
	}

	return cachedHashes, nil
}

// pruneEdges prunes all the positions that cannot exist in the prevForestRows.
func pruneEdges(hnp hashAndPos, numAdds, numLeaves uint64, forestRows, prevForestRows uint8) (hashAndPos, error) {
	prevTargetsWithHash := hashAndPos{make([]uint64, 0, hnp.Len()), make([]Hash, 0, hnp.Len())}
	for i, target := range hnp.positions {
		// Save the current row.
		row := DetectRow(target, forestRows)

		// If the row is greater than the prevForestRows, this can't exist.
		if row > prevForestRows {
			continue
		}

		currentStartPos := startPositionAtRow(row, forestRows)
		prevStartPos := startPositionAtRow(row, prevForestRows)
		offset := target - currentStartPos

		maxPos, err := maxPositionAtRow(row, prevForestRows, numLeaves-numAdds)
		if err != nil {
			return hashAndPos{}, err
		}
		if prevStartPos+offset <= maxPos {
			prevTargetsWithHash.Append(target, hnp.hashes[i])
		}
	}

	return prevTargetsWithHash, nil
}

// undoAdd remaps the targets to their previous positions and prunes positions and
// proof hashes that could not have existed before the add.
func (p *Proof) undoAdd(numAdds, numLeaves uint64, cachedHashes []Hash, toDestroy []uint64) ([]Hash, error) {
	targetsWithHash := toHashAndPos(p.Targets, cachedHashes)
	proofPos, _ := ProofPositions(targetsWithHash.positions, numLeaves, TreeRows(numLeaves))
	proofWithPos := toHashAndPos(proofPos, p.Proof)

	forestRows := TreeRows(numLeaves)
	prevForestRows := TreeRows(numLeaves - numAdds)

	// Move positions to their previous positions before the empty roots were destroyed.
	for _, destroyed := range toDestroy {
		for i, target := range targetsWithHash.positions {
			if destroyed <= target {
				continue
			}

			// If these positions are in different subtrees, continue.
			subtree, _, _, _ := DetectOffset(target, numLeaves)
			subtree1, _, _, _ := DetectOffset(destroyed, numLeaves-numAdds)
			if subtree != subtree1 {
				continue
			}
			if isAncestor(Parent(destroyed, forestRows), target, forestRows) {
				targetsWithHash.positions[i] = calcPrevPosition(target, destroyed, forestRows)
			}
		}

		for i, target := range proofWithPos.positions {
			if destroyed <= target {
				continue
			}
			// If these positions are in different subtrees, continue.
			subtree, _, _, _ := DetectOffset(target, numLeaves)
			subtree1, _, _, _ := DetectOffset(destroyed, numLeaves-numAdds)
			if subtree != subtree1 {
				continue
			}
			if isAncestor(Parent(destroyed, forestRows), target, forestRows) {
				proofWithPos.positions[i] = calcPrevPosition(target, destroyed, forestRows)
			}
		}
	}

	// Prune all positions that can't exist in the previous forest rows.
	var err error
	targetsWithHash, err = pruneEdges(targetsWithHash, numAdds, numLeaves, forestRows, prevForestRows)
	if err != nil {
		return nil, err
	}
	proofWithPos, err = pruneEdges(proofWithPos, numAdds, numLeaves, forestRows, prevForestRows)
	if err != nil {
		return nil, err
	}

	// Prune all positions that are under the previously empty root.
	for row := 0; row <= int(prevForestRows); row++ {
		for _, destroyed := range toDestroy {
			for i := 0; i < proofWithPos.Len(); i++ {
				target := proofWithPos.positions[i]
				// If these positions are in different subtrees, continue.
				subtree, _, _, _ := DetectOffset(destroyed, numLeaves)
				subtree1, _, _, _ := DetectOffset(target, numLeaves)
				if subtree == subtree1 || target == destroyed {
					proofWithPos.Delete(i)
				}
			}

			for i := 0; i < targetsWithHash.Len(); i++ {
				target := targetsWithHash.positions[i]
				// If these positions are in different subtrees, continue.
				subtree, _, _, _ := DetectOffset(destroyed, numLeaves)
				subtree1, _, _, _ := DetectOffset(target, numLeaves)
				if subtree == subtree1 || target == destroyed {
					targetsWithHash.Delete(i)
				}
			}
		}
	}

	// Remap all positions to their previous positions before the remap.
	if prevForestRows < forestRows {
		for i, pos := range targetsWithHash.positions {
			row := DetectRow(pos, TreeRows(numLeaves))

			currentStartPos := startPositionAtRow(row, forestRows)
			prevStartPos := startPositionAtRow(row, prevForestRows)

			offset := pos - currentStartPos

			targetsWithHash.positions[i] = offset + prevStartPos
		}

		for i, pos := range proofWithPos.positions {
			row := DetectRow(pos, TreeRows(numLeaves))

			currentStartPos := startPositionAtRow(row, forestRows)
			prevStartPos := startPositionAtRow(row, prevForestRows)

			offset := pos - currentStartPos

			proofWithPos.positions[i] = offset + prevStartPos
		}
	}

	// There may be extra proof hashes that we don't need anymore. Calculate the
	// needed positions and remove the rest.
	neededProofPos, _ := ProofPositions(targetsWithHash.positions, numLeaves-numAdds, prevForestRows)
	proofWithPos = getHashAndPosSubset(proofWithPos, neededProofPos)

	// Set the proof.
	p.Proof = proofWithPos.hashes
	p.Targets = targetsWithHash.positions

	return targetsWithHash.hashes, nil
}

// undoDel adds back the deleted positions and proof hashes back to the proof.
//
// NOTE undoDel does not re-cache the deleted targets that were previously cached.
func (p *Proof) undoDel(blockTargets []uint64, blockHashes, cachedHashes []Hash, blockProof Proof, numLeaves uint64) ([]Hash, error) {
	totalRows := TreeRows(numLeaves)

	if len(blockTargets) == 0 {
		return cachedHashes, nil
	}

	targetsWithHashes := toHashAndPos(p.Targets, cachedHashes)
	proofPos, _ := ProofPositions(targetsWithHashes.positions, numLeaves, totalRows)
	proofWithPos := toHashAndPos(proofPos, p.Proof)

	// Detwin the block targets.
	blockTargetsWithHash := toHashAndPos(blockTargets, blockHashes)
	blockTargetsWithHash = deTwinHashAndPos(blockTargetsWithHash, totalRows)

	// newProofs are the newly needed proofs that come from undoing the deletions.
	// Need to keep track of them separately from the current proof hashes as
	// some exisiting positions in the proof may share the same position (and thus
	// may get deduped out if we call mergeSortedHashAndPos.)
	newProofs := hashAndPos{}

	// Loop through all the targets and look for the previous sibling.
	// If that sibling is included in the proof, include the target into
	// the proof and remap the positions accordingly.
	for i := blockTargetsWithHash.Len() - 1; i >= 0; i-- {
		blockTarget, blockHash := blockTargetsWithHash.positions[i], blockTargetsWithHash.hashes[i]

		// When a target is deleted, its sibling moves up to the parent
		// position. Therefore the current sibling will be in the parent
		// position of the deleted target if it exists.
		sibPos := Parent(blockTarget, totalRows)

		// Look for the sibling in the cached targets.
		for i, target := range targetsWithHashes.positions {
			// If these positions are in different subtrees, continue.
			subtree, _, _, _ := DetectOffset(target, numLeaves)
			subtree1, _, _, _ := DetectOffset(blockTarget, numLeaves)
			if subtree != subtree1 {
				continue
			}
			if isAncestor(sibPos, target, totalRows) || sibPos == target {
				targetsWithHashes.positions[i] = calcPrevPosition(target, blockTarget, totalRows)

				// Store the block hash and target to add onto the proof hashes later.
				newProofs.Append(blockTarget, blockHash)
				sort.Sort(newProofs)

				sort.Sort(targetsWithHashes)
			}
		}

		// Look for the sibling in the proof hashes.
		for i, target := range proofWithPos.positions {
			// If these positions are in different subtrees, continue.
			subtree, _, _, _ := DetectOffset(target, numLeaves)
			subtree1, _, _, _ := DetectOffset(blockTarget, numLeaves)
			if subtree != subtree1 {
				continue
			}
			if isAncestor(sibPos, target, totalRows) || sibPos == target {
				proofWithPos.positions[i] = calcPrevPosition(target, blockTarget, totalRows)
				sibHash := proofWithPos.hashes[i]
				sort.Sort(proofWithPos)

				if isLeftNiece(blockTarget) {
					parentH := parentHash(blockHash, sibHash)
					newProof := hashAndPos{[]uint64{sibPos}, []Hash{parentH}}
					proofWithPos = mergeSortedHashAndPos(proofWithPos, newProof)

				} else {
					parentH := parentHash(sibHash, blockHash)
					newProof := hashAndPos{[]uint64{sibPos}, []Hash{parentH}}
					proofWithPos = mergeSortedHashAndPos(proofWithPos, newProof)
				}
			}
		}
	}

	// Add in the new proofs.
	proofWithPos = mergeSortedHashAndPos(proofWithPos, newProofs)

	before, _, err := calculateHashes(numLeaves, blockHashes, blockProof)
	if err != nil {
		return nil, err
	}
	beforeIdx := 0

	// Replace the proof hashes with the before hashes. This is needed
	// because the mergeSortedHashAndPos will dedupe and use the hashes
	// from proofWithPos.
	for i, pos := range proofWithPos.positions {
		for beforeIdx < before.Len() && before.positions[beforeIdx] < pos {
			beforeIdx++
		}

		if beforeIdx < before.Len() && before.positions[beforeIdx] == pos {
			proofWithPos.hashes[i] = before.hashes[beforeIdx]
		}
	}
	// Merge everything so we have a single big pile of proof hashes that
	// we can extract hashes from.
	proofWithPos = mergeSortedHashAndPos(proofWithPos, before)

	// Only extract the proof hashes that are needed for the targets after
	// the remap.
	neededProofPos, _ := ProofPositions(targetsWithHashes.positions, numLeaves, totalRows)
	proofWithPos = getHashAndPosSubset(proofWithPos, neededProofPos)

	p.Proof = proofWithPos.hashes
	p.Targets = targetsWithHashes.positions

	return targetsWithHashes.hashes, nil
}

// GetProofSubset trims away the un-needed data from the proof and returns a proof only
// for the passed in removes. An error is returned if the passed in proof does not have
// all the targets in the removes.
//
// NOTE The returned hashes and proof targets are in the same permutation as the given wants.
func GetProofSubset(proof Proof, hashes []Hash, wants []uint64, numLeaves uint64) ([]Hash, Proof, error) {
	// Copy to avoid mutating the original.
	proofTargetsCopy := copySortedFunc(proof.Targets, uint64Cmp)

	// Check that all the targets in removes are also present in the proof.
	expectedEmpty := copySortedFunc(wants, uint64Cmp)
	expectedEmpty = subtractSortedSlice(expectedEmpty, proofTargetsCopy, uint64Cmp)
	if len(expectedEmpty) > 0 {
		err := fmt.Errorf("Missing positions %v from the proof. Deletions %v, proof.Targets %v",
			expectedEmpty, wants, proof.Targets)
		return nil, Proof{}, err
	}

	// Match up the targets with their respective hashes.
	targetHashesWithPos := toHashAndPos(proofTargetsCopy, hashes)

	// calculateHashes provides us with all the intermediate calculated nodes in the tree.
	// Need to sort the returned positions and hashes as they aren't sorted.
	posAndHashes, _, err := calculateHashes(numLeaves, hashes, proof)
	if err != nil {
		return nil, Proof{}, err
	}
	sort.Sort(posAndHashes)

	// Put positions onto the proof hashes.
	positions, _ := ProofPositions(proofTargetsCopy, numLeaves, TreeRows(numLeaves))
	proofPos := toHashAndPos(positions, proof.Proof)

	// Merge the proof positions and its hashes along with the calculated intermediate nodes
	// so we have one big slice to extract the proof for the want slice.
	posAndHashes = mergeSortedHashAndPos(posAndHashes, proofPos)

	// Copy to avoid mutating the wants.
	sortedWants := copySortedFunc(wants, uint64Cmp)
	targetHashesWithPos = getHashAndPosSubset(targetHashesWithPos, sortedWants)

	// Grab the positions that we need to prove the wants.
	wantProofPos, _ := ProofPositions(targetHashesWithPos.positions, numLeaves, TreeRows(numLeaves))

	// Extract the proof positions we want and then sanity check to see that we have everything.
	posAndHashes = getHashAndPosSubset(posAndHashes, wantProofPos)
	if posAndHashes.Len() != len(wantProofPos) {
		return nil, Proof{},
			fmt.Errorf("Expected %d proofs but got %d", len(wantProofPos), posAndHashes.Len())
	}

	// Lastly, we make separate slice of hashes as we guarantee that the hashes
	// and targets will be in the same permutation as the passed in wants by the caller.
	retHashes := make([]Hash, len(wants))
	for i, want := range wants {
		idx := slices.Index(targetHashesWithPos.positions, want)
		retHashes[i] = targetHashesWithPos.hashes[idx]
	}

	return retHashes, Proof{wants, posAndHashes.hashes}, nil
}

// maybeRemap remaps the passed in hash and pos if the TreeRows increase after
// adding the new nodes.
func maybeRemap(numLeaves, numAdds uint64, hnp hashAndPos) hashAndPos {
	// Update target positions if the forest has remapped to a higher row.
	newForestRows := TreeRows(numLeaves + numAdds)
	oldForestRows := TreeRows(numLeaves)
	if newForestRows > oldForestRows {
		for i, pos := range hnp.positions {
			row := DetectRow(pos, TreeRows(numLeaves))

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
	proofPos, _ := ProofPositions(origTargetsWithHash.positions, beforeNumLeaves, TreeRows(beforeNumLeaves))
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
	neededProofPositions, _ := ProofPositions(origTargetsWithHash.positions, beforeNumLeaves+uint64(len(adds)), TreeRows(beforeNumLeaves+uint64(len(adds))))

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

// rootInfoToDestroy returns the positions of the root informations that get destroyed by
// the additions.
func rootInfoToDestroy(totalRows uint8, numAdds, numLeaves uint64, origRoots []rootInfo) [][]uint64 {
	// Check if there are any empty roots. If there are not, return early.
	exists := false
	for _, root := range origRoots {
		if root.isZombie {
			exists = true
			break
		}
	}
	if !exists {
		return nil
	}

	roots := make([]rootInfo, len(origRoots))
	copy(roots, origRoots)

	deleted := make([][]uint64, numAdds)
	for i := uint64(0); i < numAdds; i++ {
		for h := uint8(0); (numLeaves>>h)&1 == 1; h++ {
			root := roots[len(roots)-1]
			roots = roots[:len(roots)-1]
			if root.isZombie {
				rootPos := rootPosition(numLeaves, h, totalRows)
				deleted[i] = append(deleted[i], rootPos)
			}
		}
		// Just adding a non-zero value to the slice.
		roots = append(roots, rootInfo{isZombie: false})
		numLeaves++
	}

	return deleted
}

// addRootInfo modifies the root infos as if additions have been performed.
func addRootInfo(totalRows uint8, origRoots []rootInfo, numAdds uint16, numLeaves uint64) ([]rootInfo, uint64) {
	roots := make([]rootInfo, len(origRoots))
	copy(roots, origRoots)

	for i := 0; i < int(numAdds); i++ {
		pos := numLeaves

		for h := uint8(0); (numLeaves>>h)&1 == 1; h++ {
			roots = roots[:len(roots)-1]
			pos = Parent(pos, totalRows)
		}

		roots = append(roots, rootInfo{pos: pos, isZombie: false})
		numLeaves++
	}

	return roots, numLeaves
}

// delRootInfo modifies the root infos as if deletions on the passed in targets have happened.
func delRootInfo(origRoots []rootInfo, detwinedTargets []uint64) []rootInfo {
	if len(detwinedTargets) == 0 {
		return origRoots
	}

	//deTwinedPositions := copySortedFunc(targets, uint64Cmp)
	//deTwinedPositions = deTwin(deTwinedPositions, totalRows)

	for _, pos := range detwinedTargets {
		for i, root := range origRoots {
			if root.pos == pos {
				origRoots[i].isZombie = true
			}
		}
	}

	return origRoots
}

// rootInfo is just a position with a boolean to indicate if the root is a zombie.
type rootInfo struct {
	pos      uint64
	isZombie bool
}

// CSTTotalRows is the total rows that will be used for the CachingScheduleTracker.
const CSTTotalRows = 63

// ttlInfo is the position attached with its ttl value.
type ttlInfo struct {
	pos uint64
	ttl int
}

// CachingScheduleTracker keeps track of all the information needed to generate a clairvoyant caching
// schedule for downloading utreexo proofs.
type CachingScheduleTracker struct {
	deletions [][]uint64
	ttls      [][]ttlInfo
	numAdds   []uint16
	numLeaves []uint64
	toDestroy [][][]uint64
	roots     [][]rootInfo

	cacheCount        []int
	cachedCountFilled int
	schedule          [][]ttlInfo
	maxMemory         int
}

// getRoots returns the translated root positions that the desired height.
func (cs *CachingScheduleTracker) getRoots(height int32) []rootInfo {
	if height <= 0 {
		return []rootInfo{}
	}
	idx := height - 1
	roots := make([]rootInfo, len(cs.roots[idx]))
	for i, root := range cs.roots[idx] {
		roots[i] = rootInfo{
			pos:      translatePos(root.pos, CSTTotalRows, TreeRows(cs.numLeaves[idx])),
			isZombie: root.isZombie,
		}
	}

	return roots
}

// getToDestroy returns the translated todestroy roots at the desired height.
func (cs *CachingScheduleTracker) getToDestroy(height int32) []uint64 {
	if height <= 0 {
		return []uint64{}
	}
	idx := height - 1

	toDestroy := make([]uint64, 0, len(cs.toDestroy[idx]))
	for _, slice := range cs.toDestroy[idx] {
		for _, pos := range slice {
			toDestroy = append(toDestroy, translatePos(pos, CSTTotalRows, TreeRows(cs.numLeaves[idx])))
		}
	}

	return toDestroy
}

// getDels returns the translated deletions at the desired height.
func (cs *CachingScheduleTracker) getDels(height int32) []uint64 {
	if height <= 0 {
		return []uint64{}
	}
	idx := height - 1

	dels := make([]uint64, len(cs.deletions[idx]))
	for i, del := range cs.deletions[idx] {
		dels[i] = translatePos(del, CSTTotalRows, TreeRows(cs.numLeaves[idx]))
	}

	return dels
}

// AddBlockSummary takes in the deletions and the additions that are passed in and keeps track
// of them as well as keeping track of the modified root infos.
func (cs *CachingScheduleTracker) AddBlockSummary(deletions []uint64, numAdds uint16) {
	// For the first block.
	if len(cs.roots) == 0 {
		// Keep track of the block summary information.
		cs.deletions = append(cs.deletions, deletions)
		cs.numAdds = append(cs.numAdds, numAdds)

		cs.ttls = append(cs.ttls, make([]ttlInfo, 0, numAdds))
		cs.schedule = append(cs.schedule, make([]ttlInfo, 0, numAdds))
		cs.cacheCount = append(cs.cacheCount, 0)

		newRoots, newNumLeaves := addRootInfo(CSTTotalRows, []rootInfo{}, numAdds, 0)
		cs.toDestroy = append(cs.toDestroy, nil)
		cs.roots = append(cs.roots, newRoots)
		cs.numLeaves = append(cs.numLeaves, newNumLeaves)

		return
	}

	cs.ttls = append(cs.ttls, make([]ttlInfo, 0, numAdds))
	cs.schedule = append(cs.schedule, make([]ttlInfo, 0, numAdds))
	cs.cacheCount = append(cs.cacheCount, 0)
	//fmt.Println("cs.ttls", len(cs.ttls))

	numLeaves := cs.numLeaves[len(cs.numLeaves)-1]
	rows := TreeRows(numLeaves)
	translatedDels := translatePositions(deletions, rows, CSTTotalRows)
	slices.Sort(translatedDels)
	ttls := cs.incrementalGenTTLsForDels(translatedDels, len(cs.deletions))

	// Grab the current state.
	roots := make([]rootInfo, len(cs.roots[len(cs.roots)-1]))
	copy(roots, cs.roots[len(cs.roots)-1])

	// Keep track of the block summary information.
	translatedDels = deTwin(translatedDels, CSTTotalRows)
	cs.deletions = append(cs.deletions, translatedDels)
	cs.numAdds = append(cs.numAdds, numAdds)

	// Perform root info modification.
	roots = delRootInfo(roots, translatedDels)
	toDestroy := rootInfoToDestroy(CSTTotalRows, uint64(numAdds), numLeaves, roots)
	newRoots, newNumLeaves := addRootInfo(CSTTotalRows, roots, numAdds, numLeaves)

	// Keep track of the root info state.
	cs.toDestroy = append(cs.toDestroy, toDestroy)
	cs.roots = append(cs.roots, newRoots)
	cs.numLeaves = append(cs.numLeaves, newNumLeaves)

	cs.incrementalCachingSchedule(len(cs.deletions)-1, ttls)
}

// NewCachingScheduleTracker returns an initialized caching schedule tracker.
// Passed in blockCount is used to pre-allocate the underlying slices.
// Passed in maxMemory is used to set the maximum deletions the tracker will cache.
func NewCachingScheduleTracker(blockCount, maxMemory int) CachingScheduleTracker {
	return CachingScheduleTracker{
		deletions:  make([][]uint64, 0, blockCount),
		numAdds:    make([]uint16, 0, blockCount),
		ttls:       make([][]ttlInfo, 0, blockCount),
		cacheCount: make([]int, 0, blockCount),
		numLeaves:  make([]uint64, 0, blockCount),
		roots:      make([][]rootInfo, 0, blockCount),
		toDestroy:  make([][][]uint64, 0, blockCount),
		maxMemory:  maxMemory,
	}
}

//type indexedValue struct {
//	index int
//	value uint64
//}
//
//func getChildren(totalRows uint8, positions []uint64) []uint64 {
//	children := make([]uint64, 0, len(positions)*2)
//	for _, pos := range positions {
//		children = append(children, LeftChild(pos, totalRows), RightChild(pos, totalRows))
//	}
//
//	return children
//}
//
//func moveDownRow(totalRows uint8, delPos uint64, operate []uint64, positions []uint64) []uint64 {
//	for _, pos := range operate {
//		for i, val := range positions {
//			if val == pos {
//				positions[i] = calcPrevPosition(
//					val, delPos, totalRows)
//			}
//		}
//	}
//
//	return positions
//}
//
//func moveDownDescendants(totalRows uint8, deleted uint64, positions []uint64) []uint64 {
//	sibPos := Parent(deleted, totalRows)
//
//	operate := []uint64{sibPos}
//	row := DetectRow(sibPos, totalRows)
//	for h := int(row); h >= 0; h-- {
//		positions = moveDownRow(totalRows, deleted, operate, positions)
//		for _, op := range operate {
//			fmt.Println("op", op, translatePos(op, 63, 3))
//			idx := slices.Index(positions, op)
//			if idx != -1 {
//				positions[idx] = calcPrevPosition(positions[idx], deleted, totalRows)
//			}
//		}
//		operate = getChildren(totalRows, operate)
//	}
//
//	return positions
//}

//// undoDel returns the previous positions of the passed in origPositions.
////
//// NOTE: the returned origPositions keeps the original ordering.
//func undoDel(totalRows uint8, positions, deleted []uint64, numLeaves uint64) []uint64 {
//	// Nothing to do if there's no deletions.
//	if len(deleted) == 0 || len(positions) == 0 {
//		return positions
//	}
//
//	// Copy, sort, and detwin.
//	deTwinedPositions := copySortedFunc(deleted, uint64Cmp)
//	deTwinedPositions = deTwin(deTwinedPositions, totalRows)
//
//	//indexedValues := make([]indexedValue, len(positions))
//	//for i, pos := range positions {
//	//	indexedValues[i] = indexedValue{i, pos}
//	//}
//	//sort.Slice(indexedValues, func(i, j int) bool {
//	//	return indexedValues[i].value > indexedValues[j].value
//	//})
//	//fmt.Println(indexedValues)
//
//	// Loop through all the targets and look for the previous sibling.
//	// If that sibling is included in the proof, include the target into
//	// the proof and remap the positions accordingly.
//	for i := len(deTwinedPositions) - 1; i >= 0; i-- {
//		deTwinedPos := deTwinedPositions[i]
//		if isRootPositionTotalRows(deTwinedPos, numLeaves, totalRows) {
//			continue
//		}
//
//		fmt.Println("deleted", deTwinedPos, translatePos(deTwinedPos, 63, TreeRows(numLeaves)))
//		positions = moveDownDescendants(totalRows, deTwinedPos, positions)
//	}
//
//	//for _, val := range indexedValues {
//	//	positions[val.index] = val.value
//	//}
//
//	return positions
//}

// undoDel returns the previous positions of the passed in origPositions.
//
// NOTE: the returned origPositions keeps the original ordering.
func undoDel(totalRows uint8, positions, detwinedDeletions []uint64, numLeaves uint64) []uint64 {
	// Nothing to do if there's no deletions.
	if len(detwinedDeletions) == 0 || len(positions) == 0 {
		return positions
	}

	forestRows := TreeRows(numLeaves)

	// Loop through all the targets and look for the previous sibling.
	// If that sibling is included in the proof, include the target into
	// the proof and remap the positions accordingly.
	for i := len(detwinedDeletions) - 1; i >= 0; i-- {
		deTwinedPos := detwinedDeletions[i]

		// When a target is deleted, its sibling moves up to the parent
		// position. Therefore the current sibling will be in the parent
		// position of the deleted target if it exists.
		sibPos := Parent(deTwinedPos, totalRows)
		higherRow := DetectRow(sibPos, totalRows)

		//for j := idx; j >= 0; j-- {
		//	pos := positions[j]
		//	lowerRow := DetectRow(pos, totalRows)

		//	if sibPos == pos {
		//		positions[j] = calcPrevPosition(pos, deTwinedPos, totalRows)
		//		continue
		//	}

		//	if lowerRow >= higherRow {
		//		idx = j
		//		continue
		//	}

		//	parentMask := (uint64(2) << uint64(forestRows-higherRow)) - 1
		//	parentBits := (parentMask & sibPos) << uint64(higherRow)

		//	bitsToCheck := (uint64(2) << uint64(forestRows-higherRow)) - 1
		//	bitsToCheck <<= higherRow

		//	descendantBits := (bitsToCheck & pos)
		//	if descendantBits == parentBits {
		//		positions[j] = calcPrevPosition(pos, deTwinedPos, totalRows)
		//	}
		//}

		//slices.Sort(positions)

		for j, pos := range positions {
			if sibPos == pos {
				positions[j] = calcPrevPosition(pos, deTwinedPos, totalRows)
				continue
			}

			lowerRow := DetectRow(pos, totalRows)
			if higherRow < lowerRow {
				continue
			}

			parentMask := (uint64(2) << uint64(forestRows-higherRow)) - 1
			parentBits := (parentMask & sibPos) << uint64(higherRow)

			bitsToCheck := (uint64(2) << uint64(forestRows-higherRow)) - 1
			bitsToCheck <<= higherRow

			descendantBits := (bitsToCheck & pos)
			if descendantBits == parentBits {
				positions[j] = calcPrevPosition(pos, deTwinedPos, totalRows)
			}

			//if doesDelAffectPosition(sibPos, pos, numLeaves, totalRows) {
			//	positions[j] = calcPrevPosition(pos, deTwinedPos, totalRows)
			//}
		}
	}

	return positions
}

// moveDownPositions moves the positions in the cached slice to where they were
// before the delPos was removed.
//
// NOTE: the returned positions keeps the original ordering.
func moveDownPositions(totalRows uint8, position, delPos, numLeaves uint64, cached []uint64) []uint64 {
	for i, pos := range cached {
		if doesDelAffectPosition(position, pos, numLeaves, totalRows) {
			cached[i] = calcPrevPosition(pos, delPos, totalRows)
		}
	}

	return cached
}

func undoSingleAdd(totalRows uint8, positions []uint64, toDestroy []uint64, numLeaves uint64) (
	[]uint64, int) {

	removedPosIdx := -1
	for _, destroy := range toDestroy {
		positions = moveDownPositions(totalRows, Parent(destroy, totalRows), destroy, numLeaves, positions)
	}

	index := slices.Index(positions, numLeaves-1)
	if index != -1 {
		removedPosIdx = index
	}

	return positions, removedPosIdx
}

//// undoSingleAdd undoes a single addition. The returned values are the positions reverted
//// back before the leaf was added, the toDestroy minus the roots that were place back in,
//// and the index of the leaf in positions if it exists.
////
//// NOTE: the returned positions keeps the original ordering.
//func undoSingleAdd(totalRows uint8, positions, toDestroy []uint64, numLeaves uint64) (
//	[]uint64, []uint64, int) {
//
//	pos := numLeaves - 1
//	removedPosIdx := -1
//	if len(toDestroy) == 0 {
//		index := slices.Index(positions, pos)
//		if index != -1 {
//			removedPosIdx = index
//		}
//		return positions, toDestroy, removedPosIdx
//	}
//
//	// We work our way down from the root that's being removed.
//	subtree := detectSubtree(pos, numLeaves, totalRows)
//	subtreeRows := subtreeRow(numLeaves, uint8(subtree))
//	pos = rootPosition(numLeaves, subtreeRows, totalRows)
//
//	for row := int(subtreeRows); row >= 0; row-- {
//		// Check if we have an empty root to place back in.
//		possibleRoot := LeftChild(pos, totalRows)
//		index := slices.Index(toDestroy, possibleRoot)
//		if index != -1 {
//			toDestroy = slices.Delete(toDestroy, index, index+1)
//			positions = moveDownPositions(totalRows, pos, possibleRoot, numLeaves, positions)
//
//			if len(toDestroy) == 0 {
//				row = 0
//				pos = numLeaves - 1
//			}
//		}
//
//		// Check if this leaf is in the positions.
//		if row == 0 {
//			index = slices.Index(positions, pos)
//			if index != -1 {
//				removedPosIdx = index
//			}
//		}
//
//		pos = RightChild(pos, totalRows)
//	}
//
//	return positions, toDestroy, removedPosIdx
//}

//// undoAdd reverts the numAdds amount of additions. The returned values are the positions reverted
//// back before the leaves were added, all the indexes of the positions that were created.
////
//// NOTE: the returned positions keeps the original ordering.
//func undoAdd(totalRows uint8, positions, origToDestroy []uint64, numAdds uint16, numLeaves uint64) ([]uint64, []int) {
//	// Don't modify the passed in toDestroy.
//	toDestroy := copySortedFunc(origToDestroy, uint64Cmp)
//
//	created := make([]int, 0, len(positions))
//	for i := 0; i < int(numAdds); i++ {
//		var idx int
//		positions, toDestroy, idx = undoSingleAdd(totalRows, positions, toDestroy, numLeaves)
//		if idx != -1 {
//			created = append(created, idx)
//		}
//		numLeaves--
//	}
//
//	return positions, created
//}

// undoAdd reverts the numAdds amount of additions. The returned values are the positions reverted
// back before the leaves were added, all the indexes of the positions that were created.
//
// NOTE: the returned positions keeps the original ordering.
func undoAdd(totalRows uint8, positions []uint64, origToDestroy [][]uint64, numAdds uint16, numLeaves uint64) ([]uint64, []uint64) {
	created := make([]uint64, 0, len(positions))

	if len(origToDestroy) == 0 {
		for i := 0; i < int(numAdds); i++ {
			numLeaves--
			idx := slices.Index(positions, numLeaves)
			if idx != -1 {
				created = append(created, positions[idx])
				positions = slices.Delete(positions, idx, idx+1)
			}
		}

		return positions, created
	}

	for i := int(numAdds) - 1; i >= 0; i-- {
		for _, destroy := range origToDestroy[i] {
			positions = moveDownPositions(totalRows, Parent(destroy, totalRows), destroy, numLeaves, positions)
			slices.Sort(positions)
		}

		numLeaves--
		for i, pos := range positions {
			if pos == numLeaves {
				created = append(created, positions[i])
				positions = slices.Delete(positions, i, i+1)
				break
			}

			if pos > numLeaves-1 {
				break
			}
		}
	}

	return positions, created
}

// getPrevPos returns the previous positions of the given cached slice before the
// addition and the deletions have been performed as well as the indexes of the
// positions that were created in the block.
//
// NOTE: the returned positions keeps the original ordering.
func getPrevPos(totalRows uint8, cached, deleted []uint64, toDestroy [][]uint64, numAdds uint16, numLeaves uint64) ([]uint64, []uint64) {
	var created []uint64
	cached, created = undoAdd(totalRows, cached, toDestroy, numAdds, numLeaves)
	cached = undoDel(totalRows, cached, deleted, numLeaves-uint64(numAdds))
	return cached, created
}

//func (cs *CachingScheduleTracker) genTTLsForDels(dels []uint64, index int) {
//	cached := make([]uint64, len(dels))
//	copy(cached, dels)
//
//	xy := make([][2]int, 0, len(cached))
//	for i := range cached {
//		xy = append(xy, [2]int{index, i})
//	}
//
//	for i := len(cs.deletions) - 1; i >= 0; i-- {
//		deletions := cs.deletions[i]
//		numAdds := cs.numAdds[i]
//		numLeaves := cs.numLeaves[i]
//		toDestroy := cs.toDestroy[i]
//
//		// Revert the cached positions by a block.
//		var created []uint64
//		cached, created = getPrevPos(
//			CSTTotalRows, cached, deletions, toDestroy, numAdds, numLeaves)
//
//		// Set ttls. We go backwards since the undo undoes the bigger positions first.
//		for j := len(createdIdxs) - 1; j >= 0; j-- {
//			idx := createdIdxs[j]
//
//			cords := xy[idx]
//
//			deletedAt := cords[0]
//			createdAt := i
//			ttl := deletedAt - createdAt
//
//			//fmt.Printf("created %v at %v\n", cached[idx], i)
//
//			cs.ttls[i] = append(cs.ttls[i], ttlInfo{
//				pos: cached[idx],
//				ttl: ttl,
//			})
//
//			sort.Slice(cs.ttls[i], func(a, b int) bool {
//				return cs.ttls[i][a].pos < cs.ttls[i][b].pos
//			})
//		}
//
//		// Remove the created positions from the cache.
//		slices.Sort(createdIdxs)
//		for i, idx := range createdIdxs {
//			useIdx := idx - i
//			cached = slices.Delete(cached, useIdx, useIdx+1)
//			xy = slices.Delete(xy, useIdx, useIdx+1)
//		}
//
//		if len(cached) == 0 {
//			break
//		}
//	}
//}

func (cs *CachingScheduleTracker) incrementalGenTTLsForDels(dels []uint64, index int) []ttlInfo {
	// Copy to avoid modifying the original.
	cached := make([]uint64, len(dels))
	copy(cached, dels)

	// For the deletions that wasn't cached. If we don't do better than
	// these, we can give up figuring out the ttls.
	sawNotCachedTTLs := make([]ttlInfo, 0, len(dels))

	ttls := make([]ttlInfo, 0, len(dels))

	for i := len(cs.deletions) - 1; i >= 0; i-- {
		deletions := cs.deletions[i]
		numAdds := cs.numAdds[i]
		numLeaves := cs.numLeaves[i]
		toDestroy := cs.toDestroy[i]

		currentTTL := index - i

		// Range through the currently saved not cached ttls.
		for _, notCachedTTL := range sawNotCachedTTLs {
			// If something wasn't cached and it has a lower or equal TTL, then
			// none of the current dels are gonna be cached. Quit now to save
			// on compute.
			if notCachedTTL.ttl <= currentTTL {
				return ttls
			}
		}

		// Range through the ttls for the deletions that happened here.
		for _, notCachedTTL := range cs.ttls[i] {
			// If something wasn't cached and it has a lower or equal TTL, then
			// none of the current dels are gonna be cached. Quit now to save
			// on compute.
			if notCachedTTL.ttl <= currentTTL {
				return ttls
			}

			sawNotCachedTTLs = append(sawNotCachedTTLs, notCachedTTL)
		}

		if i < cs.cachedCountFilled {
			return ttls
		}

		// Give up if this can't be cached because the cache is already full.
		if cs.cacheCount[i] >= cs.maxMemory {
			cs.cachedCountFilled = i
			return ttls
		}

		// Revert the cached positions by a block.
		var created []uint64
		cached, created = getPrevPos(
			CSTTotalRows, cached, deletions, toDestroy, numAdds, numLeaves)

		// Set ttls.
		for _, create := range created {
			deletedAt := index
			createdAt := i
			ttl := deletedAt - createdAt

			ttls = append(ttls, ttlInfo{
				pos: create,
				ttl: ttl,
			})
		}

		if len(cached) == 0 {
			break
		}
	}

	sort.Slice(ttls, func(a, b int) bool {
		return ttls[a].pos < ttls[b].pos
	})
	return ttls
}

func (cs *CachingScheduleTracker) cacheCountOk(start, end int) bool {
	if end < cs.cachedCountFilled {
		return false
	}

	for i := start; i < end; i++ {
		if cs.cacheCount[i] >= cs.maxMemory {
			cs.cachedCountFilled = i
			return false
		}
	}

	return true
}

func (cs *CachingScheduleTracker) incrementalCachingSchedule(index int, ttls []ttlInfo) {
	sort.Slice(ttls, func(i, j int) bool {
		return ttls[i].ttl < ttls[j].ttl
	})

	for i := 0; i < len(ttls); i++ {
		ttl := ttls[i]

		createBlock := index - ttl.ttl
		if cs.cacheCountOk(createBlock, index) {
			cs.schedule[createBlock] = append(cs.schedule[createBlock], ttl)
			sort.Slice(cs.schedule[createBlock], func(i, j int) bool {
				return cs.schedule[createBlock][i].pos < cs.schedule[createBlock][j].pos
			})

			for j := createBlock; j < index; j++ {
				cs.cacheCount[j] += 1
				if cs.cacheCount[j] >= cs.maxMemory {
					cs.cachedCountFilled = j
				}
			}

			ttls = slices.Delete(ttls, i, i+1)
			i--
		} else {
			cs.ttls[index] = append(cs.ttls[index], ttl)
			sort.Slice(cs.ttls[index], func(a, b int) bool {
				return cs.ttls[index][a].pos < cs.ttls[index][b].pos
			})
		}
	}
}

//func (cs *CachingScheduleTracker) genTTLsForDels(dels []uint64, index int) {
//	cached := make([]uint64, len(dels))
//	copy(cached, dels)
//
//	xy := make([][2]int, 0, len(cached))
//	for i := range cached {
//		xy = append(xy, [2]int{index, i})
//	}
//
//	for i := len(cs.deletions) - 1; i >= 0; i-- {
//		deletions := cs.deletions[i]
//		numAdds := cs.numAdds[i]
//		numLeaves := cs.numLeaves[i]
//		toDestroy := cs.toDestroy[i]
//
//		// Revert the cached positions by a block.
//		var createdIdxs []int
//		cached, createdIdxs = getPrevPos(
//			CSTTotalRows, cached, deletions, toDestroy, numAdds, numLeaves)
//
//		// Set ttls. We go backwards since the undo undoes the bigger positions first.
//		for j := len(createdIdxs) - 1; j >= 0; j-- {
//			idx := createdIdxs[j]
//
//			cords := xy[idx]
//
//			deletedAt := cords[0]
//			createdAt := i
//			ttl := deletedAt - createdAt
//
//			//fmt.Printf("created %v at %v\n", cached[idx], i)
//
//			cs.ttls[i] = append(cs.ttls[i], ttlInfo{
//				pos: cached[idx],
//				ttl: ttl,
//			})
//
//			sort.Slice(cs.ttls[i], func(a, b int) bool {
//				return cs.ttls[i][a].pos < cs.ttls[i][b].pos
//			})
//		}
//
//		// Remove the created positions from the cache.
//		slices.Sort(createdIdxs)
//		for i, idx := range createdIdxs {
//			useIdx := idx - i
//			cached = slices.Delete(cached, useIdx, useIdx+1)
//			xy = slices.Delete(xy, useIdx, useIdx+1)
//		}
//
//		if len(cached) == 0 {
//			break
//		}
//	}
//}

//// genTTLs creates the ttl values for the deletions. Only the numAdds that we know is spent
//// will have ttls.
//func (cs *CachingScheduleTracker) genTTLs() {
//	// Init ttls.
//	cs.ttls = make([][]ttlInfo, len(cs.numAdds))
//
//	// cached contains the deletions that we'll be reverting each block until
//	// we get to the position that it started off as. xy cointains the corresponding
//	// xy values for each of the position in the cached slice.
//	cached := make([]uint64, 0, len(cs.deletions))
//	xy := make([][2]int, 0, len(cs.deletions))
//
//	for i := len(cs.deletions) - 1; i >= 0; i-- {
//		//fmt.Println("genttl on block", i)
//		deletions := cs.deletions[i]
//		numAdds := cs.numAdds[i]
//		numLeaves := cs.numLeaves[i]
//		toDestroy := cs.toDestroy[i]
//
//		// Revert the cached positions by a block.
//		var createdIdxs []int
//		cached, createdIdxs = getPrevPos(
//			CSTTotalRows, cached, deletions, toDestroy, numAdds, numLeaves)
//
//		// Set ttls. We go backwards since the undo undoes the bigger positions first.
//		for j := len(createdIdxs) - 1; j >= 0; j-- {
//			idx := createdIdxs[j]
//
//			cords := xy[idx]
//
//			deletedAt := cords[0]
//			createdAt := i
//			ttl := deletedAt - createdAt
//
//			cs.ttls[i] = append(cs.ttls[i], ttlInfo{
//				pos: cached[idx],
//				ttl: ttl,
//			})
//		}
//
//		// Remove the created positions from the cache.
//		slices.Sort(createdIdxs)
//		for i, idx := range createdIdxs {
//			useIdx := idx - i
//			cached = slices.Delete(cached, useIdx, useIdx+1)
//			xy = slices.Delete(xy, useIdx, useIdx+1)
//		}
//
//		// Append new deletions.
//		cached = append(cached, deletions...)
//		for j := range deletions {
//			xy = append(xy, [2]int{i, j})
//		}
//	}
//}

func (c *CachingScheduleTracker) TTLString() string {
	var sb strings.Builder
	sb.WriteString("CachingScheduleTracker:\n")

	// Write ttls
	sb.WriteString("  ttls:\n")
	for i, ttl := range c.ttls {
		sb.WriteString(fmt.Sprintf("    [%d]: %v\n",
			i, ttl))
	}

	sb.WriteString("  cache schedules:\n")
	for i, sch := range c.schedule {
		sb.WriteString(fmt.Sprintf("    [%d]: %v\n",
			i, sch))
	}

	return sb.String()
}

// String returns the CachingScheduleTracker as a formatting string.
func (c *CachingScheduleTracker) String() string {
	var sb strings.Builder

	sb.WriteString("CachingScheduleTracker:\n")

	// Write deletions
	sb.WriteString("  deletions:\n")
	for i, del := range c.deletions {
		sb.WriteString(fmt.Sprintf("    [%d]: %v (translated %v)\n",
			i, del, translatePositions(del, CSTTotalRows, TreeRows(c.numLeaves[i]))))
	}

	// Write ttls
	sb.WriteString("  ttls:\n")
	for i, ttl := range c.ttls {
		sb.WriteString(fmt.Sprintf("    [%d]: %v\n",
			i, ttl))
	}

	sb.WriteString("  cache schedules:\n")
	for i, sch := range c.schedule {
		sb.WriteString(fmt.Sprintf("    [%d]: %v\n",
			i, sch))
	}

	// Write numAdds
	sb.WriteString(fmt.Sprintf("  numAdds: %v\n", c.numAdds))

	// Write numLeaves
	sb.WriteString(fmt.Sprintf("  numLeaves: %v\n", c.numLeaves))

	// Write toDestroy
	sb.WriteString("  toDestroy:\n")
	//for i, td := range c.toDestroy {
	//	sb.WriteString(fmt.Sprintf("    [%d]: %v (translated %v)\n",
	//		i, td, translatePositions(td, CSTTotalRows, TreeRows(c.numLeaves[i]))))
	//}

	for i, tds := range c.toDestroy {
		sb.WriteString(fmt.Sprintf("    %d:\n", i))
		for _, td := range tds {
			sb.WriteString(fmt.Sprintf("    [%d]: %v (translated %v)\n",
				i, td, translatePositions(td, CSTTotalRows, TreeRows(c.numLeaves[i]))))
			sb.WriteString("]\n")
		}
		sb.WriteString("\n")
	}

	// Write roots
	sb.WriteString("  roots:\n")
	for i, rootList := range c.roots {
		sb.WriteString(fmt.Sprintf("    [%d]: [", i))
		for j, root := range rootList {
			if j > 0 {
				sb.WriteString(", ")
			}
			sb.WriteString(fmt.Sprintf("{pos: %d (translated %d), isZombie: %t}",
				root.pos, translatePos(root.pos, CSTTotalRows, TreeRows(c.numLeaves[i])),
				root.isZombie))
		}
		sb.WriteString("]\n")
	}

	return sb.String()
}

func (cs *CachingScheduleTracker) GetCachingSchedule() [][]uint64 {
	schedule := make([][]uint64, len(cs.schedule))
	for i, s := range cs.schedule {
		uint64S := make([]uint64, 0, len(s))
		for _, elem := range s {
			uint64S = append(uint64S, elem.pos)
		}
		schedule[i] = uint64S
	}

	return schedule
}

// GenerateCachingSchedule returns the positions that the client should cache to have an optimal
// caching for the passed in maxMemory.
//
// NOTE: maxMemory represents how many targets that the user would like to cache.
func (cs *CachingScheduleTracker) GenerateCachingSchedule(maxMemory int) [][]uint64 {
	cachingSch := make([][]ttlInfo, len(cs.numAdds))

	cache := make([]ttlInfo, 0, maxMemory)
	createHeights := make(map[uint64]int, maxMemory)
	for i, ttls := range cs.ttls {
		//fmt.Println("gencaching schedule on block", i)

		// Check the cache for spent positions.
		for j := 0; j < len(cache); j++ {
			// TTL value decremented by one.
			cache[j].ttl -= 1

			// If the position is spent here, then we add it to the
			// caching schedule.
			if cache[j].ttl == 0 {
				height := createHeights[cache[j].pos]
				delete(createHeights, cache[j].pos)
				cachingSch[height] = append(cachingSch[height], cache[j])
				//slices.Sort(cachingSch[height])

				cache = slices.Delete(cache, j, j+1)
				j--
			}
		}

		// Operate on the ttls in this block.
		for _, ttl := range ttls {
			// Easy path if the cache is free.
			if len(cache) < maxMemory {
				cache = append(cache, ttl)
				createHeights[ttl.pos] = i
				continue
			}

			// If the cache is full, check if we can replace a value with
			// a greater ttl.
			for k := range cache {
				if cache[k].ttl > ttl.ttl {
					// Remove.
					delete(createHeights, cache[k].pos)
					cache = slices.Delete(cache, k, k+1)

					// Replace.
					cache = append(cache, ttl)
					createHeights[ttl.pos] = i

					break
				}
			}
		}
	}

	//return cachingSch
	return nil
}
