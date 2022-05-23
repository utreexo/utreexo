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

// ToString for debugging, shows the proof
func (p *Proof) ToString() string {
	targs := make([]uint64, len(p.Targets))
	copy(targs, p.Targets)
	sort.Slice(targs, func(a, b int) bool { return targs[a] < targs[b] })

	s := fmt.Sprintf("%d targets: ", len(targs))
	for _, t := range targs {
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
	proofPositions := proofPositions(sortedTargets, p.numLeaves, treeRows(p.numLeaves))

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

// toHashAndPos returns a slice of hash and pos that's sorted.
func toHashAndPos(targets []uint64, hashes []Hash) []hashAndPos {
	hnp := make([]hashAndPos, len(hashes))

	for i := range hnp {
		hnp[i].hash = hashes[i]
		hnp[i].pos = targets[i]
	}

	sort.Slice(hnp, func(a, b int) bool { return hnp[a].pos < hnp[b].pos })

	return hnp
}

// Verify calculates the root hashes from the passed in proof and delHashes and
// compares it against the current roots in the pollard.
func (p *Pollard) Verify(delHashes []Hash, proof Proof) error {
	if len(delHashes) == 0 {
		return nil
	}

	rootHashes := calculateRoots(p.numLeaves, delHashes, proof)
	if len(rootHashes) == 0 {
		return fmt.Errorf("Pollard.Verify fail. No roots calculated "+
			"but have %d deletions", len(delHashes))
	}

	err := verify(rootHashes, p.roots)
	if err != nil {
		return fmt.Errorf("Pollard.Verify fail. Error %s", err)
	}

	return nil
}

// verify takes compares the root polnodes with the root candidates. Errors out if all the
// rootCandidates do not have a corresponding polnode with the same hash.
func verify(rootCandidates []Hash, currentRoots []*polNode) error {
	rootMatches := 0
	for i := range currentRoots {
		if len(rootCandidates) > rootMatches &&
			currentRoots[len(currentRoots)-(i+1)].data == rootCandidates[rootMatches] {
			rootMatches++
		}
	}
	if len(rootCandidates) != rootMatches {
		// The proof is invalid because some root candidates were not
		// included in `roots`.
		err := fmt.Errorf("Have %d roots but only "+
			"matched %d roots", len(rootCandidates), rootMatches)
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

		proves := mergeSortedHashAndPos(nextProves, extractedProves)
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

func mergeSortedHashAndPos(a []hashAndPos, b []hashAndPos) (c []hashAndPos) {
	maxa := len(a)
	maxb := len(b)

	// shortcuts:
	if maxa == 0 {
		return b
	}
	if maxb == 0 {
		return a
	}

	// make it (potentially) too long and truncate later
	c = make([]hashAndPos, maxa+maxb)

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
		if vala.pos < valb.pos { // a is less so append that
			c[j] = vala
			idxa++
		} else if vala.pos > valb.pos { // b is less so append that
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

func mergeSortedNodeAndPos(a []nodeAndPos, b []nodeAndPos) (c []nodeAndPos) {
	maxa := len(a)
	maxb := len(b)

	// shortcuts:
	if maxa == 0 {
		return b
	}
	if maxb == 0 {
		return a
	}

	// make it (potentially) too long and truncate later
	c = make([]nodeAndPos, maxa+maxb)

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
		if vala.pos < valb.pos { // a is less so append that
			c[j] = vala
			idxa++
		} else if vala.pos > valb.pos { // b is less so append that
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

// calculateRootsAfterDel returns the accumulator roots after the targets in the proof
// has been deleted.
func calculateRootsAfterDel(numLeaves uint64, proof Proof) ([]Hash, error) {
	delHashes, afterProof, err := proofAfterDeletion(numLeaves, proof)
	if err != nil {
		return nil, err
	}

	roots := calculateRoots(numLeaves, delHashes, afterProof)
	return roots, nil
}

// proofAfterDeletion modifies the proof so that it proves the siblings of the targets
// in this proof. Having this information allows for the calculation of roots after the
// deletion has happened.
func proofAfterDeletion(numLeaves uint64, proof Proof) ([]Hash, Proof, error) {
	forestRows := treeRows(numLeaves)
	proofPos := proofPositions(proof.Targets, numLeaves, forestRows)

	// Copy the targets to avoid mutating the original. Then detwin it
	// to prep for deletion.
	targets := make([]uint64, len(proof.Targets))
	copy(targets, proof.Targets)
	targets = deTwin(targets, forestRows)

	proveTargets := make([]uint64, 0, len(targets))
	targetHashes := make([]Hash, 0, len(targets))

	hnp := toHashAndPos(proofPos, proof.Proof)
	for i := 0; i < len(targets); i++ {
		if isRootPosition(targets[i], numLeaves, forestRows) {
			break
		}

		sib := sibling(targets[i])

		// Look for the sibling in the proof hashes.
		idx := slices.IndexFunc(hnp, func(elem hashAndPos) bool { return elem.pos == sib })
		if idx != -1 {
			parentPos := parent(sib, forestRows)
			if len(proveTargets) > 0 && proveTargets[len(proveTargets)-1] == leftSib(parentPos) {
				proveTargets[len(proveTargets)-1] = parent(parentPos, forestRows)

				pHash := parentHash(targetHashes[len(targetHashes)-1], hnp[idx].hash)
				targetHashes[len(targetHashes)-1] = pHash
			} else {
				proveTargets = append(proveTargets, parentPos)
				targetHashes = append(targetHashes, hnp[idx].hash)
			}

			// Delete the sibling from hnp.
			hnp = append(hnp[:idx], hnp[idx+1:]...)
		} else {
			// If the sibling is not in the proof hashes, it's in the targets.
			idx := slices.IndexFunc(proveTargets, func(elem uint64) bool { return elem == sib })
			if idx != -1 {
				proveTargets[idx] = parent(proveTargets[idx], forestRows)
			} else {
				return nil, Proof{}, fmt.Errorf("proofAfterDeletion error: Couldn't find expected pos of %d", sib)
			}
		}
	}

	hashes := make([]Hash, len(hnp))
	for i := range hnp {
		hashes[i] = hnp[i].hash
	}

	return targetHashes, Proof{proveTargets, hashes}, nil
}

// cachedHashUpdateList returns the cached nodes that should be updated after deletion.
func (p *Pollard) cachedHashUpdateList() ([]nodeAndPos, error) {
	forestRows := treeRows(p.numLeaves)

	// Map to keep track of what's already in the slice to avoid duplicates.
	posMap := make(map[uint64]interface{})

	// The nodes that will need to have their hashes checked for updates.
	updateNodes := make([]nodeAndPos, 0, len(p.nodeMap))
	for _, node := range p.nodeMap {
		pos := p.calculatePosition(node)
		_, found := posMap[pos]
		if !found {
			updateNodes = append(updateNodes, nodeAndPos{node, pos})
			posMap[pos] = nil
		}

		sibPos := sibling(pos)
		_, found = posMap[sibPos]
		if found {
			// If the sibling is in the map, we can skip following up the
			// aunts as they share the same aunts.
			continue
		}
		posMap[sibPos] = nil

		sibNode, err := node.getSibling()
		if err != nil {
			return nil, err
		}
		updateNodes = append(updateNodes, nodeAndPos{sibNode, sibPos})

		// Keep adding aunts until we get to the root.
		for node.aunt != nil {
			pos = sibling(parent(pos, forestRows))
			node = node.aunt

			_, found = posMap[pos]
			if found {
				continue
			}

			posMap[pos] = nil
			updateNodes = append(updateNodes, nodeAndPos{node, pos})
		}
	}

	sort.Slice(updateNodes, func(a, b int) bool { return updateNodes[a].pos < updateNodes[b].pos })
	return updateNodes, nil
}
