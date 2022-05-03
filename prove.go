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
	slices.Sort(targs)
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
	// No hashes to prove means that the proof is empty.
	if len(hashes) == 0 {
		return Proof{}, nil
	}
	// No proof needed for an accumulator that has one leaf or less.
	if p.numLeaves <= 1 {
		return Proof{}, nil
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
		//fmt.Printf("calculated %d for hash %s\n",
		//	proof.Targets[i], hex.EncodeToString(node.data[:]))
	}

	// Sort the targets as the proof hashes need to be sorted.
	//
	// TODO find out if sorting and losing in-block position information hurts
	// locality or performance.
	sortedTargets := make([]uint64, len(proof.Targets))
	copy(sortedTargets, proof.Targets)
	slices.Sort(sortedTargets)

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

func (p *Pollard) VerifyAndPopulate(delHashes []Hash, proof Proof) error {
	//fmt.Println("numLeaves", p.numLeaves)
	if len(delHashes) == 0 {
		return nil
	}
	toProve := make([]nodeAndPos, len(delHashes))

	for i := range toProve {
		toProve[i].node = &polNode{data: delHashes[i]}
		toProve[i].pos = proof.Targets[i]
	}

	sort.Slice(toProve, func(a, b int) bool { return toProve[a].pos < toProve[b].pos })

	rootNodes := p.calculateNodes(toProve, proof.Proof)
	if len(rootNodes) == 0 {
		return fmt.Errorf("No roots calculated but has %d deletions", len(delHashes))
	}

	//for i, rootHash := range rootNodes {
	//	fmt.Printf("root %d, hash %s\n", i, hex.EncodeToString(rootHash.data[:]))
	//}

	rootMatches := 0
	for i := range p.roots {
		if len(rootNodes) > rootMatches &&
			p.roots[len(p.roots)-(i+1)].data == rootNodes[rootMatches].data {
			rootMatches++
		}
	}
	if len(rootNodes) != rootMatches {
		// the proof is invalid because some root candidates were not
		// included in `roots`.
		err := fmt.Errorf("VerifyAndPopulate error: generated %d roots but only"+
			"matched %d roots", len(rootNodes), rootMatches)
		return err
	}

	return nil
}

func (p *Pollard) populate(rootNodes []*polNode) error {
	idx := 0
	for _, rn := range p.roots {
		if rn.data == rootNodes[idx].data {
			idx++
		}
	}
	return nil
}

func (p *Pollard) pop() {
}

func (p *Pollard) calculateNodes(toProve []nodeAndPos, proofHashes []Hash) []*polNode {
	//fmt.Println(p.String())
	calculatedRootNodes := make([]*polNode, 0, len(p.roots))
	totalRows := treeRows(p.numLeaves)

	var nextNodes []nodeAndPos
	for row := 0; row <= int(totalRows); row++ {
		extractedNodes := extractRowNode(toProve, totalRows, uint8(row))

		proves := mergeSortedNodeAndPos(nextNodes, extractedNodes)
		nextNodes = nextNodes[:0]

		for i := 0; i < len(proves); i++ {
			prove := proves[i]

			// This means we hashed all the way to the top of this subtree.
			if isRootPosition(prove.pos, p.numLeaves, totalRows) {
				calculatedRootNodes = append(calculatedRootNodes, prove.node)
				continue
			}

			// Check if the next prove is the sibling of this prove.
			if i+1 < len(proves) && rightSib(prove.pos) == proves[i+1].pos {
				swapNieces(prove.node, proves[i+1].node)
				nextNode := nodeAndPos{
					node: &polNode{
						data:   parentHash(prove.node.data, proves[i+1].node.data),
						lNiece: prove.node,
						rNiece: proves[i+1].node,
					},
					pos: parent(prove.pos, totalRows),
				}
				updateAunt(nextNode.node)
				nextNodes = append(nextNodes, nextNode)

				i++ // Increment one more since we procesed another prove.
			} else {
				hash := proofHashes[0]
				proofHashes = proofHashes[1:]

				proofNode := &polNode{data: hash}
				swapNieces(prove.node, proofNode)

				nextNode := nodeAndPos{pos: parent(prove.pos, totalRows)}
				if isLeftNiece(prove.pos) {
					nextNode.node = &polNode{
						data:   parentHash(prove.node.data, hash),
						lNiece: prove.node,
						rNiece: proofNode,
					}
				} else {
					nextNode.node = &polNode{
						data:   parentHash(hash, prove.node.data),
						lNiece: proofNode,
						rNiece: prove.node,
					}
				}

				updateAunt(nextNode.node)
				nextNodes = append(nextNodes, nextNode)
			}
		}
	}

	return calculatedRootNodes
}

type hashAndPos struct {
	hash Hash
	pos  uint64
}

func (p *Pollard) Verify(delHashes []Hash, proof Proof) error {
	if len(delHashes) == 0 {
		return nil
	}
	toProve := make([]hashAndPos, len(delHashes))

	for i := range toProve {
		toProve[i].hash = delHashes[i]
		toProve[i].pos = proof.Targets[i]
	}

	sort.Slice(toProve, func(a, b int) bool { return toProve[a].pos < toProve[b].pos })

	rootHashes := p.calculateRoots(toProve, proof.Proof)
	if len(rootHashes) == 0 {
		return fmt.Errorf("No roots calculated but has %d deletions", len(delHashes))
	}

	//for i, rootHash := range rootHashes {
	//	fmt.Printf("root %d, hash %s\n", i, hex.EncodeToString(rootHash[:]))
	//}

	rootMatches := 0
	for i := range p.roots {
		if len(rootHashes) > rootMatches &&
			p.roots[len(p.roots)-(i+1)].data == rootHashes[rootMatches] {
			rootMatches++
		}
	}
	if len(rootHashes) != rootMatches {
		// the proof is invalid because some root candidates were not
		// included in `roots`.
		err := fmt.Errorf("Pollard.Verify: generated %d roots but only"+
			"matched %d roots", len(rootHashes), rootMatches)
		return err
	}

	return nil
}

func (p *Pollard) calculateRoots(toProve []hashAndPos, proofHashes []Hash) []Hash {
	calculatedRootHashes := make([]Hash, 0, len(p.roots))
	totalRows := treeRows(p.numLeaves)

	var nextProves []hashAndPos
	for row := 0; row <= int(totalRows); row++ {
		extractedProves := extractRowHash(toProve, totalRows, uint8(row))

		proves := mergeSortedHashAndPos(nextProves, extractedProves)
		nextProves = nextProves[:0]

		for i := 0; i < len(proves); i++ {
			prove := proves[i]

			// This means we hashed all the way to the top of this subtree.
			if isRootPosition(prove.pos, p.numLeaves, totalRows) {
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
				hash := proofHashes[0]
				proofHashes = proofHashes[1:]

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
