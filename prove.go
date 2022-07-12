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
	if len(hashes) == 0 || p.numLeaves == 0 {
		return Proof{}, nil
	}
	// A Pollard with 1 leaf has no proof and only 1 target.
	if p.numLeaves == 1 {
		return Proof{Targets: []uint64{0}}, nil
	}

	var proof Proof
	proof.Targets = make([]uint64, len(hashes))

	// Grab the positions of the hashes that are to be proven.
	for i, wanted := range hashes {
		node, ok := p.nodeMap[wanted.mini()]
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
	proofPositions, _ := proofPositions(sortedTargets, p.numLeaves, treeRows(p.numLeaves))

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

type hashAndPos struct {
	hash Hash
	pos  uint64
}

// hashAndPosCmp compares the elements of a and b.
// The result is 0 if a == b, -1 if a < b, and +1 if a > b.
func hashAndPosCmp(a, b hashAndPos) int {
	if a.pos < b.pos {
		return -1
	} else if a.pos > b.pos {
		return 1
	}
	return 0
}

// toHashAndPos returns a slice of hash and pos that's sorted.
func toHashAndPos(targets []uint64, hashes []Hash) []hashAndPos {
	hnp := make([]hashAndPos, len(hashes))

	for i := range hnp {
		hnp[i].hash = hashes[i]
		hnp[i].pos = targets[i]
	}

	// No guarantee that the targets and the delHashes are in order. Sort them
	// before processing.
	sort.Slice(hnp, func(a, b int) bool { return hnp[a].pos < hnp[b].pos })

	return hnp
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

	rootCandidates := calculateRoots(p.numLeaves, delHashes, proof)
	if len(rootCandidates) == 0 {
		return fmt.Errorf("Pollard.Verify fail. No roots calculated "+
			"but have %d deletions", len(delHashes))
	}

	rootMatches := 0
	for i := range p.roots {
		if len(rootCandidates) > rootMatches &&
			p.roots[len(p.roots)-(i+1)].data == rootCandidates[rootMatches] {
			rootMatches++
		}
	}
	// Error out if all the rootCandidates do not have a corresponding
	// polnode with the same hash.
	if len(rootCandidates) != rootMatches {
		rootHashes := make([]Hash, len(p.roots))
		for i := range rootHashes {
			rootHashes[i] = p.roots[i].data
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

// calculateRoots calculates and returns the root hashes.
func calculateRoots(numLeaves uint64, delHashes []Hash, proof Proof) []Hash {
	totalRows := treeRows(numLeaves)

	// Where all the root hashes that we've calculated will go to.
	calculatedRootHashes := make([]Hash, 0, numRoots(numLeaves))

	// Where all the parent hashes we've calculated in a given row will go to.
	nextProves := make([]hashAndPos, 0, len(delHashes))

	// These are the leaves to be proven. Each represent a position and the
	// hash of a leaf.
	toProve := toHashAndPos(proof.Targets, delHashes)

	// Separate index for the hashes in the passed in proof.
	proofHashIdx := 0
	for row := 0; row <= int(totalRows); row++ {
		extractedProves := extractRowHash(toProve, totalRows, uint8(row))

		proves := mergeSortedSlicesFunc(nextProves, extractedProves, hashAndPosCmp)
		nextProves = nextProves[:0]

		for i := 0; i < len(proves); i++ {
			prove := proves[i]

			// This means we hashed all the way to the top of this subtree.
			if isRootPosition(prove.pos, numLeaves, totalRows) {
				calculatedRootHashes = append(calculatedRootHashes, prove.hash)
				continue
			}

			// Check if the next prove is the sibling of this prove.
			if i+1 < len(proves) && rightSib(prove.pos) == proves[i+1].pos {
				nextProve := hashAndPos{
					hash: parentHash(prove.hash, proves[i+1].hash),
					pos:  parent(prove.pos, totalRows),
				}
				nextProves = append(nextProves, nextProve)

				i++ // Increment one more since we procesed another prove.
			} else {
				// If the next prove isn't the sibling of this prove, we fetch
				// the next proof hash to calculate the parent.
				hash := proof.Proof[proofHashIdx]
				proofHashIdx++

				nextProve := hashAndPos{pos: parent(prove.pos, totalRows)}
				if isLeftNiece(prove.pos) {
					nextProve.hash = parentHash(prove.hash, hash)
				} else {
					nextProve.hash = parentHash(hash, prove.hash)
				}

				nextProves = append(nextProves, nextProve)
			}
		}
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

func extractRowHash(toProve []hashAndPos, forestRows, rowToExtract uint8) []hashAndPos {
	if len(toProve) < 0 {
		return []hashAndPos{}
	}

	start := -1
	end := 0

	for i := 0; i < len(toProve); i++ {
		if detectRow(toProve[i].pos, forestRows) == rowToExtract {
			if start == -1 {
				start = i
			}

			end = i
		} else {
			// If we're not at the desired row and start has already been set
			// once, that means we've extracted everything we can. This is
			// possible because the assumption is that the toProve are sorted.
			if start != -1 {
				break
			}
		}
	}

	if start == -1 {
		return []hashAndPos{}
	}

	count := (end + 1) - start
	row := make([]hashAndPos, count)

	copy(row, toProve[start:end+1])

	return row
}

func extractRowNode(toProve []nodeAndPos, forestRows, rowToExtract uint8) []nodeAndPos {
	if len(toProve) < 0 {
		return []nodeAndPos{}
	}

	start := -1
	end := 0

	for i := 0; i < len(toProve); i++ {
		if detectRow(toProve[i].pos, forestRows) == rowToExtract {
			if start == -1 {
				start = i
			}

			end = i
		} else {
			// If we're not at the desired row and start has already been set
			// once, that means we've extracted everything we can. This is
			// possible because the assumption is that the toProve are sorted.
			if start != -1 {
				break
			}
		}
	}

	if start == -1 {
		return []nodeAndPos{}
	}

	count := (end + 1) - start
	row := make([]nodeAndPos, count)

	copy(row, toProve[start:end+1])

	return row
}

func removeDuplicateInt(uint64Slice []uint64) []uint64 {
	allKeys := make(map[uint64]bool)
	list := []uint64{}
	for _, item := range uint64Slice {
		if _, value := allKeys[item]; !value {
			allKeys[item] = true
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
	targetsWithHashes = subtractSortedSlice(targetsWithHashes, remTargets,
		func(a hashAndPos, b uint64) int {
			if a.pos < b {
				return -1
			} else if a.pos > b {
				return 1
			}
			return 0
		})

	// Detwin the removes.
	deTwinedRems := make([]uint64, len(remTargets))
	copy(deTwinedRems, remTargets)
	deTwinedRems = deTwin(deTwinedRems, forestRows)

	// Final step of the detwin. Add the detwined target and hash to targetsWithHashes.
	// Empty hashes are just so that they can also be hashAndPos. All of these will get
	// removed and be replaced with the sibling so it's ok with have empty hashes.
	deTwinedRemsWithHash := toHashAndPos(deTwinedRems, make([]Hash, len(deTwinedRems)))
	targetsWithHashes = mergeSortedSlicesFunc(targetsWithHashes, deTwinedRemsWithHash, hashAndPosCmp)

	// For each of the detwinedRems, if we find it in targetsWithHashes, we'll try
	// to find the sibling in the proof hashes and promote it as the parent. If
	// it's not in the proof hashes, we'll move the descendants of the existing
	// proofs of the sibling's parent up by one row.
	for i := 0; i < len(deTwinedRems); i++ {
		// If this deletion isn't in the targets, move on.
		idx := slices.IndexFunc(targetsWithHashes, func(elem hashAndPos) bool { return elem.pos == deTwinedRems[i] })
		if idx == -1 {
			continue
		}
		targetPos := targetsWithHashes[idx].pos
		targetsWithHashes = append(targetsWithHashes[:idx], targetsWithHashes[idx+1:]...)

		// If we're deleting a root, then add empty to the targets and move on.
		if isRootPosition(deTwinedRems[i], numLeaves, forestRows) {
			targetsWithHashes = mergeSortedSlicesFunc(targetsWithHashes, []hashAndPos{{empty, deTwinedRems[i]}}, hashAndPosCmp)
			continue
		}

		// Same for whenthe sibling is a root. Add empty and move on.
		sib := sibling(targetPos)
		if isRootPosition(sib, numLeaves, forestRows) {
			targetsWithHashes = mergeSortedSlicesFunc(targetsWithHashes, []hashAndPos{{empty, sib}}, hashAndPosCmp)
			continue
		}

		// Look for the sibling in the proof hashes.
		if idx := slices.IndexFunc(hnp, func(elem hashAndPos) bool { return elem.pos == sib }); idx != -1 {
			parentPos := parent(sib, forestRows)

			targetsWithHashes = mergeSortedSlicesFunc(targetsWithHashes, []hashAndPos{{hnp[idx].hash, parentPos}}, hashAndPosCmp)

			// Delete the sibling from hnp as this sibling is a target now, not a proof.
			hnp = append(hnp[:idx], hnp[idx+1:]...)
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
			for j := len(targetsWithHashes) - 1; j >= 0; j-- {
				ancestor := isAncestor(parent(sib, forestRows), targetsWithHashes[j].pos, forestRows)
				if ancestor {
					// We can ignore the error since we've already verified that
					// the targetsWithHashes[j] is an ancestor of sib.
					nextPos, _ := calcNextPosition(targetsWithHashes[j].pos, sib, forestRows)
					targetsWithHashes[j].pos = nextPos
				}
			}

			// Update the proofs as well.
			for j := len(hnp) - 1; j >= 0; j-- {
				ancestor := isAncestor(parent(sib, forestRows), hnp[j].pos, forestRows)
				if ancestor {
					// We can ignore the error since we've already verified that
					// the hnp[j] is an ancestor of sib.
					nextPos, _ := calcNextPosition(hnp[j].pos, sib, forestRows)
					hnp[j].pos = nextPos
				}
			}

			// Dedupe.
			sort.Slice(targetsWithHashes, func(a, b int) bool { return targetsWithHashes[a].pos < targetsWithHashes[b].pos })
			for i := 0; i < len(targetsWithHashes); i++ {
				if i < len(targetsWithHashes)-1 && targetsWithHashes[i] == targetsWithHashes[i+1] {
					targetsWithHashes = append(targetsWithHashes[:i], targetsWithHashes[i+1:]...)
				}
			}
		}
	}

	// The proof hashes should be in order before they're included in the proof.
	sort.Slice(hnp, func(a, b int) bool { return hnp[a].pos < hnp[b].pos })

	// The leftover proofs that weren't siblings of the detwined targets are
	// the new proofs for the new targets.
	hashes := make([]Hash, len(hnp))
	for i := range hnp {
		hashes[i] = hnp[i].hash
	}

	// Extract hashes and targets.
	targetHashes := make([]Hash, len(targetsWithHashes))
	for i := range targetHashes {
		targetHashes[i] = targetsWithHashes[i].hash
	}
	proveTargets := make([]uint64, len(targetsWithHashes))
	for i := range proveTargets {
		proveTargets[i] = targetsWithHashes[i].pos
	}

	return targetHashes, Proof{proveTargets, hashes}
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
func hashSiblings(proofHashes []hashAndPos, hnp hashAndPos, sibHash Hash, forestRows uint8) []hashAndPos {
	// Calculate the parent hash and the position.
	var hash Hash
	if isLeftNiece(hnp.pos) {
		hash = parentHash(hnp.hash, sibHash)
	} else {
		hash = parentHash(sibHash, hnp.hash)
	}
	pos := parent(hnp.pos, forestRows)
	proofHashes = append(proofHashes, hashAndPos{hash, pos})

	// Go through the proofHashes and look for siblings of the newly hashed parent.
	// If we find the sibling, we'll hash with the sibling to get the parent until we
	// no longer find siblings.
	idx := slices.IndexFunc(proofHashes, func(hnp hashAndPos) bool { return hnp.pos == sibling(pos) })
	for idx != -1 {
		// Calculate the parent hash and the position.
		if isLeftNiece(pos) {
			hash = parentHash(hash, proofHashes[idx].hash)
		} else {
			hash = parentHash(proofHashes[idx].hash, hash)
		}
		pos = parent(pos, forestRows)

		// Pop off the last appended proofHash and the sibling since
		// we hashed up.
		proofHashes = append(proofHashes[:len(proofHashes)-1], proofHashes[len(proofHashes):]...)
		proofHashes = append(proofHashes[:idx], proofHashes[idx+1:]...)

		// Append the newly created parent.
		proofHashes = append(proofHashes, hashAndPos{hash, pos})

		// Look for the sibling of the newly created parent.
		idx = slices.IndexFunc(proofHashes, func(hnp hashAndPos) bool { return hnp.pos == sibling(pos) })
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
	proofHashesWithPos = mergeSortedSlicesFunc(proofHashesWithPos, targetHashesWithPos, hashAndPosCmp)

	// Remove the remTargets from the targets.
	targetHashesWithPos = subtractSortedSlice(targetHashesWithPos, remTargets,
		func(a hashAndPos, b uint64) int {
			if a.pos < b {
				return -1
			} else if a.pos > b {
				return 1
			}
			return 0
		})
	// Extract hashes and positions.
	targetHashes := make([]Hash, len(targetHashesWithPos))
	for i := range targetHashes {
		targetHashes[i] = targetHashesWithPos[i].hash
	}
	targets = make([]uint64, len(targetHashesWithPos))
	for i := range targets {
		targets[i] = targetHashesWithPos[i].pos
	}

	// Get rid of all the leftover targets from the proofs.
	proofHashesWithPos = subtractSortedSlice(proofHashesWithPos, targets,
		func(a hashAndPos, b uint64) int {
			if a.pos < b {
				return -1
			} else if a.pos > b {
				return 1
			}
			return 0
		})
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
	for i := 0; i < len(proofHashesWithPos); i++ {
		proof := proofHashesWithPos[i]
		subTree, _, _, _ := detectOffset(proof.pos, numLeaves)

		if !slices.Contains(subTrees, subTree) {
			idx := slices.IndexFunc(proofHashesWithPos, func(elem hashAndPos) bool { return elem.pos == proof.pos })
			proofHashesWithPos = append(proofHashesWithPos[:idx], proofHashesWithPos[idx+1:]...)
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
		if proofIdx >= len(proofHashesWithPos) {
			break
		}

		proofHash := proofHashesWithPos[proofIdx]
		removePosition := removePositions[i]

		if removePosition == proofHash.pos {
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
			if proofIdx < len(proofHashesWithPos)-1 && proofHashesWithPos[proofIdx+1].pos == rightSib(proofHash.pos) {
				proofHashesWithPos = hashSiblings(proofHashesWithPos, proofHash, proofHashesWithPos[proofIdx+1].hash, forestRows)

				proofHashesWithPos = append(proofHashesWithPos[:proofIdx], proofHashesWithPos[proofIdx+2:]...)
			} else if proofIdx >= 1 && proofHashesWithPos[proofIdx-1].pos == leftSib(proofHash.pos) {
				proofHashesWithPos = hashSiblings(proofHashesWithPos, proofHash, proofHashesWithPos[proofIdx-1].hash, forestRows)

				proofHashesWithPos = append(proofHashesWithPos[:proofIdx-1], proofHashesWithPos[proofIdx+1:]...)
				proofIdx-- // decrement since we're taking out an element from the left side.
			} else {
				// If there are no siblings present, just remove it.
				proofHashesWithPos = append(proofHashesWithPos[:proofIdx], proofHashesWithPos[proofIdx+1:]...)
			}

			sort.Slice(proofHashesWithPos, func(a, b int) bool { return proofHashesWithPos[a].pos < proofHashesWithPos[b].pos })
		} else if removePosition < proofHash.pos {
			continue
		} else {
			proofIdx++
			i--
		}
	}

	// Extract only the hashes.
	sort.Slice(proofHashesWithPos, func(a, b int) bool { return proofHashesWithPos[a].pos < proofHashesWithPos[b].pos })
	proofHashes := make([]Hash, len(proofHashesWithPos))
	for i := range proofHashes {
		proofHashes[i] = proofHashesWithPos[i].hash
	}

	return targetHashes, Proof{targets, proofHashes}
}

// AddProof adds the newProof onto the existing proof and return the new cachedDelHashes and proof. Newly calculateable
// positions and duplicates are excluded in the returned proof.
func AddProof(proofA, proofB Proof, targetHashesA, targetHashesB []Hash, numLeaves uint64) ([]Hash, Proof) {
	totalRows := treeRows(numLeaves)

	// Calculate proof hashes for proof A and add positions to the proof hashes.
	targetsA := copySortedFunc(proofA.Targets, uint64Less)
	proofPosA, calculateableA := proofPositions(targetsA, numLeaves, totalRows)
	proofAndPosA := toHashAndPos(proofPosA, proofA.Proof)

	// Calculate proof hashes for proof B and add positions to the proof hashes.
	targetsB := copySortedFunc(proofB.Targets, uint64Less)
	proofPosB, calculateableB := proofPositions(targetsB, numLeaves, totalRows)
	proofAndPosB := toHashAndPos(proofPosB, proofB.Proof)

	// Add the proof hashes of proofA and proofB.
	proofAndPosC := mergeSortedSlicesFunc(proofAndPosA, proofAndPosB, hashAndPosCmp)

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
	proofAndPosC = subtractSortedSlice(proofAndPosC, calculateableC,
		func(a hashAndPos, b uint64) int {
			if a.pos < b {
				return -1
			} else if a.pos > b {
				return 1
			}
			return 0
		})

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
	proofAndPosC = subtractSortedSlice(proofAndPosC, targetsC,
		func(a hashAndPos, b uint64) int {
			if a.pos < b {
				return -1
			} else if a.pos > b {
				return 1
			}
			return 0
		})

	// Extract the proof hashes.
	proofHashes := make([]Hash, len(proofAndPosC))
	for i := range proofHashes {
		proofHashes[i] = proofAndPosC[i].hash
	}
	retProof := Proof{targetsC, proofHashes}

	// Get the hashes for the targets.
	cachedDelHashAndPosA := toHashAndPos(proofA.Targets, targetHashesA)
	cachedDelHashAndPosB := toHashAndPos(proofB.Targets, targetHashesB)
	cachedDelHashAndPosC := mergeSortedSlicesFunc(cachedDelHashAndPosA, cachedDelHashAndPosB, hashAndPosCmp)

	retDelHashes := make([]Hash, len(cachedDelHashAndPosC))
	for i := range retDelHashes {
		retDelHashes[i] = cachedDelHashAndPosC[i].hash
	}

	return retDelHashes, retProof
}

// UpdateProofRemove modifies the cached proof with the deletions that happen in the block proof.
// It updates the necessary proof hashes and un-caches the targets that are being deleted.
func UpdateProofRemove(cachedProof, blockProof Proof, cachedDelHashes, blockDelHashes []Hash, numLeaves uint64) ([]Hash, Proof) {
	// First we calculate which hashes are going to be deleted from the cached hashes.
	// The resulting desiredHashesWithPos are the hashes that we will be caching after
	// the deletion.
	desiredHashesWithPos := toHashAndPos(cachedProof.Targets, cachedDelHashes)
	blockHashesWithPos := toHashAndPos(blockProof.Targets, blockDelHashes)
	desiredHashesWithPos = subtractSortedSlice(desiredHashesWithPos, blockHashesWithPos, hashAndPosCmp)

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
	blockDelHashesWithPos = removeHashes(blockDelHashesWithPos, desiredHashesWithPos, func(elem hashAndPos) Hash { return elem.hash })
	removeTargets := make([]uint64, len(blockDelHashesWithPos))
	for i, hashWithPos := range blockDelHashesWithPos {
		removeTargets[i] = hashWithPos.pos
	}

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
func UpdateProofAdd(cachedProof Proof, adds []Hash, stump Stump) Proof {
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

	// Create a map of all the proof positions and their hashes. We'll use this
	// map to fetch the needed proof positions after the addition.
	proofPos, _ := proofPositions(cachedProof.Targets, stump.NumLeaves, newForestRows)
	newRootsMap := make(map[uint64]Hash)
	for i, pos := range proofPos {
		newRootsMap[pos] = cachedProof.Proof[i]
	}

	roots := stump.Roots
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
				pos := rootPosition(stump.NumLeaves, h, newForestRows)

				sib := sibling(pos)
				for j := len(cachedProof.Targets) - 1; j >= 0; j-- {
					ancestor := isAncestor(parent(sib, newForestRows), cachedProof.Targets[j], newForestRows)
					if ancestor {
						// We can ignore the error since we've already verified that
						// the cachedProof.Targets[j] is an ancestor of sib.
						nextPos, _ := calcNextPosition(cachedProof.Targets[j], sib, newForestRows)
						cachedProof.Targets[j] = nextPos
					}
				}
				cachedProof.Targets = removeDuplicateInt(cachedProof.Targets)

				tmpMap := make(map[uint64]Hash)
				for key, hash := range newRootsMap {
					ancestor := isAncestor(parent(sib, newForestRows), key, newForestRows)
					if ancestor {
						// We can ignore the error since we've already verified that
						// the proofAndPos[j] is an ancestor of sib.
						nextPos, _ := calcNextPosition(key, sib, newForestRows)
						tmpMap[nextPos] = hash
					} else {
						tmpMap[key] = hash
					}
				}
				newRootsMap = tmpMap

				continue
			} else {
				pos := rootPosition(stump.NumLeaves, h, newForestRows)

				if _, found := newRootsMap[pos]; !found {
					newRootsMap[pos] = root
				}
				if _, found := newRootsMap[pos^1]; !found {
					newRootsMap[pos^1] = newRoot
				}

				// Calculate the hash of the new root and append it.
				newRoot = parentHash(root, newRoot)
				pos = parent(pos, newForestRows)

				if _, found := newRootsMap[pos]; !found {
					newRootsMap[pos] = newRoot
				}
			}
		}
		roots = append(roots, newRoot)
		stump.NumLeaves++
	}
	// These are the positions that we'd need after the addition.
	cachedProofTargets := copySortedFunc(cachedProof.Targets, uint64Less)
	neededProofPositions, _ := proofPositions(cachedProofTargets, stump.NumLeaves, newForestRows)

	proofHashes := make([]Hash, len(neededProofPositions))
	for i, neededProofPosition := range neededProofPositions {
		hash := newRootsMap[neededProofPosition]
		proofHashes[i] = hash
	}

	cachedProof.Proof = proofHashes

	return cachedProof
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

	blockHashes, blockProof := proofAfterDeletion(stump.NumLeaves, blockProof)
	rootCandidates := calculateRoots(stump.NumLeaves, blockHashes, blockProof)

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
	adds []Hash, stump Stump) ([]Hash, Proof, error) {

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
	cachedProof = UpdateProofAdd(cachedProof, adds, stump)

	return cachedDelHashes, cachedProof, nil
}
