package utreexo

import (
	"encoding/hex"
	"fmt"
	"sort"
)

// Pollard is a representation of the utreexo forest using a collection of
// binary trees. It may or may not contain the entire set.
type Pollard struct {
	// nodeMap maps hashes to polNodes. Used during proving individual elements
	// in the accumulator.
	nodeMap map[miniHash]*polNode

	// roots are the roots of each tree in the forest.
	//
	// NOTE: Since roots don't have nieces, they point to children.
	// In the below tree, 06 is the root and it points to its children,
	// 04 and 05. However, 04 points to 02 and 03; 05 points to 00 and 01.
	// 04 and 05 are pointing to their nieces.
	//
	// 06
	// |-------\
	// 04      05
	// |---\   |---\
	// 00  01  02  03
	roots []*polNode

	// numLeaves is the number of all leaves that were ever added to the accumulator.
	numLeaves uint64

	// numDels is the number of all elements that were deleted from the accumulator.
	numDels uint64

	// full indicates that this pollard will keep all the leaves in the accumulator.
	// Only Pollards that have the full value set to true will be able to prove all
	// the elements.
	full bool
}

// NewAccumulator returns a initialized accumulator. To enable the generating proofs
// for all elements, set full to true.
func NewAccumulator(full bool) Pollard {
	var p Pollard
	p.nodeMap = make(map[miniHash]*polNode)
	p.full = full

	return p
}

// Modify takes in the additions and deletions and updates the accumulator accordingly.
//
// NOTE Modify does NOT do any validation and assumes that all the positions of the leaves
// being deleted have already been verified.
func (p *Pollard) Modify(adds []Leaf, delHashes []Hash, origDels []uint64) error {
	// Make a copy to avoid mutating the deletion slice passed in.
	delCount := len(origDels)
	dels := make([]uint64, delCount)
	copy(dels, origDels)

	// Remove the delHashes from the map.
	p.deleteFromMap(delHashes)

	// Perform the deletion. It's important that this must happen before the addition.
	err := p.remove(dels)
	if err != nil {
		return err
	}
	p.numDels += uint64(delCount)

	p.add(adds)

	return nil
}

// add adds all the passed in leaves to the accumulator.
func (p *Pollard) add(adds []Leaf) {
	for _, add := range adds {
		// Create a node from the hash. If the pollard is full, then remember
		// every node.
		node := &polNode{data: add.Hash, remember: add.Remember}
		if p.full {
			node.remember = true
		}

		// Add the hash to the map if this node is supposed to be remembered.
		if node.remember {
			p.nodeMap[add.mini()] = node
		}

		newRoot := p.calculateNewRoot(node)
		p.roots = append(p.roots, newRoot)

		// Increment as we added a leaf.
		p.numLeaves++
	}
}

// calculateNewRoot adds the node to the accumulator and calculates the new root.
func (p *Pollard) calculateNewRoot(node *polNode) *polNode {
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
	for h := uint8(0); (p.numLeaves>>h)&1 == 1; h++ {
		// Grab and pop off the root that will become a node.
		// NOTE Explicitly not niling out the polNode for GC as we still need it.
		root := p.roots[len(p.roots)-1]
		p.roots = p.roots[:len(p.roots)-1]

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
		if root.data == empty {
			continue
		}

		// Roots point to their children. Those children become nieces here.
		swapNieces(root, node)

		// Calculate the hash of the new root.
		nHash := parentHash(root.data, node.data)

		newRoot := &polNode{data: nHash, lNiece: root, rNiece: node}
		if p.full {
			newRoot.remember = true
		}

		// Set aunt.
		updateAunt(newRoot)
		newRoot.prune()
		node = newRoot
	}

	return node
}

// remove removes all the positions that are passed in.
func (p *Pollard) remove(dels []uint64) error {
	sort.Slice(dels, func(a, b int) bool { return dels[a] < dels[b] })

	totalRows := treeRows(p.numLeaves)
	dels = deTwin(dels, totalRows)

	for _, del := range dels {
		// If a root is being deleted, then we mark it and all the leaves below
		// it to be deleted.
		if isRootPosition(del, p.numLeaves, totalRows) {
			err := p.deleteRoot(del)
			if err != nil {
				return err
			}
		} else {
			err := p.deleteSingle(del)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

// delete root removes all the pointers to and from this root and places an
// empty hash at this root.
func (p *Pollard) deleteRoot(del uint64) error {
	tree, _, _, err := detectOffset(del, p.numLeaves)
	if err != nil {
		return err
	}
	if tree > uint8(len(p.roots)-1) {
		return fmt.Errorf("getNode error: couldn't fetch %d, "+
			"calculated root index of %d but only have %d roots",
			del, tree, len(p.roots))
	}

	// Delete from map.
	delete(p.nodeMap, p.roots[tree].data.mini())

	if p.roots[tree].lNiece != nil {
		p.roots[tree].lNiece.aunt = nil
	}
	if p.roots[tree].rNiece != nil {
		p.roots[tree].rNiece.aunt = nil
	}
	p.roots[tree].chop()
	p.roots[tree].aunt = nil
	p.roots[tree].data = empty

	return nil
}

// deleteSingle deletes one leaf from the accumulator and re-hashes the root.
func (p *Pollard) deleteSingle(del uint64) error {
	// Fetch all the needed nodes.
	from := sibling(del)
	fromNode, fromNodeSib, _, err := p.getNode(from)
	if err != nil {
		return err
	}
	toNode, err := fromNodeSib.getParent()
	if err != nil {
		return err
	}
	toSib := fromNodeSib.aunt

	// If the position I'm moving to has an aunt, I'm not becoming a root.
	if toNode.aunt != nil {
		// Move myself up.
		transferAunt(fromNode, toNode)
		transferNiece(fromNode, toNode)

		// Move my children up.
		transferNiece(toSib, fromNodeSib)

		updateAunt(toNode.aunt)
	} else {
		// My data is given to the root.
		*toNode = *fromNode

		// Get my children from my sibling as I'm a root now.
		transferNiece(toNode, fromNodeSib)

		// Update all the nieces to point at me.
		updateAunt(toNode)

		// Delete my former self.
		delNode(fromNode)

		// If the node was a leaf, update the map to point to the root.
		_, found := p.nodeMap[toNode.data.mini()]
		if found {
			p.nodeMap[toNode.data.mini()] = toNode
		}
	}

	// Delete the node from the map.
	delete(p.nodeMap, fromNodeSib.data.mini())
	delNode(fromNodeSib)

	// If to position is a root, there's no parent hash to be calculated so
	// return early.
	totalRows := treeRows(p.numLeaves)
	to := parent(del, totalRows)
	if isRootPosition(to, p.numLeaves, totalRows) {
		toNode.aunt = nil
		return nil
	}
	parentNode, err := toNode.getParent()
	if err != nil {
		return err
	}

	// Set aunt.
	toNode.aunt, err = parentNode.getSibling()
	if err != nil {
		return err
	}

	// If there's no sibling, it means that toNode is a children of
	// the root. Make it point to the parent.
	if toNode.aunt == nil {
		toNode.aunt = parentNode
	}

	// Hash this node and all the parents/ancestors of this node.
	err = hashToRoot(parentNode)
	if err != nil {
		return err
	}

	return nil
}

// deleteFromMap deletes the hashes passed in from the node map.
func (p *Pollard) deleteFromMap(delHashes []Hash) {
	for _, del := range delHashes {
		delete(p.nodeMap, del.mini())
	}
}

// Undo reverts the most recent modify that happened to the accumulator.
func (p *Pollard) Undo(numAdds uint64, dels []uint64, delHashes []Hash, prevRoots []Hash) error {
	for i := 0; i < int(numAdds); i++ {
		p.undoSingleAdd()
	}
	err := p.undoEmptyRoots(numAdds, dels, prevRoots)
	if err != nil {
		return err
	}

	err = p.undoDels(dels, delHashes)
	if err != nil {
		return err
	}

	return nil
}

// undoEmptyRoots places empty roots back in after undoing the additions.
func (p *Pollard) undoEmptyRoots(numAdds uint64, origDels []uint64, prevRoots []Hash) error {
	if len(p.roots) >= int(numRoots(p.numLeaves)) {
		return nil
	}

	// Add empty roots that was present in the previous roots.
	for i, prevRoot := range prevRoots {
		if prevRoot == empty {
			if i >= len(p.roots) {
				p.roots = append(p.roots, &polNode{remember: p.full})
			}
			if p.roots[i].data != empty {
				p.roots = append(p.roots, nil)
				copy(p.roots[i+1:], p.roots[i:])
				p.roots[i] = &polNode{data: prevRoot, remember: p.full}
			}
		}
	}

	dels := make([]uint64, len(origDels))
	copy(dels, origDels)

	// Sort before detwining.
	sort.Slice(dels, func(a, b int) bool { return dels[a] < dels[b] })
	dels = deTwin(dels, treeRows(p.numLeaves))

	// Add empty roots that were destroyed during the additions. Need to do this
	// separate step before the deletions are undo-ed.
	for i := len(dels) - 1; i >= 0; i-- {
		del := dels[i]
		if isRootPosition(del, p.numLeaves, treeRows(p.numLeaves)) {
			tree, _, _, err := detectOffset(del, p.numLeaves)
			if err != nil {
				return err
			}
			if int(tree) == len(p.roots) {
				p.roots = append(p.roots, &polNode{data: empty, remember: p.full})
			}
			if int(tree) > len(p.roots) {
				return fmt.Errorf("undoEmptyRoots error: calculated root index of %d "+
					"for position %d but only have %d roots",
					tree, del, len(p.roots))
			}
			if p.roots[tree].data != empty {
				p.roots = append(p.roots, nil)
				copy(p.roots[tree+1:], p.roots[tree:])
				p.roots[tree] = &polNode{data: empty, remember: p.full}
			}
		}
	}

	return nil
}

// undoSingleAdd undoes one leaf that was added to the accumulator.
func (p *Pollard) undoSingleAdd() {
	lowestRootRow := getLowestRoot(p.numLeaves)
	for row := int(lowestRootRow); row >= 0; row-- {
		lowestRoot := p.roots[len(p.roots)-1]
		p.roots = p.roots[:len(p.roots)-1]

		lNiece, rNiece := lowestRoot.lNiece, lowestRoot.rNiece

		if lNiece != nil {
			swapNieces(lNiece, rNiece)
			lNiece.aunt, rNiece.aunt = nil, nil
			p.roots = append(p.roots, lNiece, rNiece)
		} else {
			row = -1
		}

		delete(p.nodeMap, lowestRoot.data.mini())
		delNode(lowestRoot)
	}
	p.numLeaves--
}

func (p *Pollard) undoDels(dels []uint64, delHashes []Hash) error {
	if len(dels) != len(delHashes) {
		return fmt.Errorf("Got %d targets to be deleted but have %d hashes",
			len(dels), len(delHashes))
	}

	pnps := make([]nodeAndPos, len(dels))
	for i := range dels {
		pn := &polNode{data: delHashes[i], remember: p.full}
		pnps[i] = nodeAndPos{pn, dels[i]}

		p.nodeMap[delHashes[i].mini()] = pn
	}
	sort.Slice(pnps, func(a, b int) bool { return pnps[a].pos < pnps[b].pos })

	totalRows := treeRows(p.numLeaves)
	pnps = deTwinPolNode(pnps, totalRows)

	// Go through all the de-twined nodes and all from the highest position first.
	for i := len(pnps) - 1; i >= 0; i-- {
		pnp := pnps[i]

		if isRootPosition(pnp.pos, p.numLeaves, treeRows(p.numLeaves)) {
			tree, _, _, err := detectOffset(pnp.pos, p.numLeaves)
			if err != nil {
				return err
			}
			p.roots[tree] = pnp.node
			continue
		} else {
			err := p.undoSingleDel(pnp.node, pnp.pos)
			if err != nil {
				return err
			}
		}
	}

	p.numDels -= uint64(len(delHashes))

	return nil
}

func (p *Pollard) undoSingleDel(node *polNode, pos uint64) error {
	totalRows := treeRows(p.numLeaves)

	siblingPos := parent(pos, totalRows)
	sibling, aunt, _, err := p.getNode(siblingPos)
	if err != nil {
		return fmt.Errorf("Couldn't undo %s at position %d, err: %v",
			hex.EncodeToString(node.data[:]), pos, err)
	}

	pHash := calculateParentHash(pos, node, sibling)
	parent := &polNode{data: pHash, remember: p.full}

	// If the original parent of the deleted node is not a root.
	if sibling.aunt != nil {
		transferAunt(parent, sibling)
		transferNiece(parent, sibling)
		updateAunt(parent)

		auntLNiece := aunt.lNiece
		auntRNiece := aunt.rNiece
		if isLeftNiece(pos) {
			aunt.lNiece = node
			aunt.rNiece = sibling
		} else {
			aunt.lNiece = sibling
			aunt.rNiece = node
		}
		updateAunt(aunt)

		transferNiece(sibling, node)

		node.lNiece = auntLNiece
		node.rNiece = auntRNiece
		updateAunt(node)
	} else {
		// We're moving the parent to sibling position.
		*sibling, *parent = *parent, *sibling
		sibling, parent = parent, sibling

		if isLeftNiece(pos) {
			parent.lNiece = node
			parent.rNiece = sibling
		} else {
			parent.lNiece = sibling
			parent.rNiece = node
		}
		updateAunt(parent)
		updateAunt(sibling)

		swapNieces(parent.lNiece, parent.rNiece)

		_, found := p.nodeMap[sibling.data.mini()]
		if found {
			p.nodeMap[sibling.data.mini()] = sibling
		}

		return nil
	}

	err = hashToRoot(parent)
	if err != nil {
		return err
	}

	return nil
}

// GetRoots returns the hashes of all the roots.
func (p *Pollard) GetRoots() []Hash {
	roots := make([]Hash, 0, len(p.roots))

	for _, root := range p.roots {
		roots = append(roots, root.data)
	}

	return roots
}

// GetTotalCount returns the count of all the polNodes in the pollard.
func (p *Pollard) GetTotalCount() int64 {
	var size int64
	for _, root := range p.roots {
		size += getCount(root)
	}

	return size
}
