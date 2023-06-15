package utreexo

import (
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"
	"sort"
)

// Pollard is a representation of the utreexo forest using a collection of
// binary trees. It may or may not contain the entire set.
type Pollard struct {
	// NodeMap maps hashes to polNodes. Used during proving individual elements
	// in the accumulator.
	NodeMap map[miniHash]*polNode

	// Roots are the roots of each tree in the forest.
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
	Roots []*polNode

	// NumLeaves is the number of all leaves that were ever added to the accumulator.
	NumLeaves uint64

	// NumDels is the number of all elements that were deleted from the accumulator.
	NumDels uint64

	// Full indicates that this pollard will keep all the leaves in the accumulator.
	// Only Pollards that have the Full value set to true will be able to prove all
	// the elements.
	Full bool

	// RequiredNodes is a list of nodes that are required to prove the accumulator.
	RequiredNodes []*polNode
}

// NewAccumulator returns a initialized accumulator. To enable the generating proofs
// for all elements, set Full to true.
func NewAccumulator(full bool) Pollard {
	var p Pollard
	p.NodeMap = make(map[miniHash]*polNode)
	p.Full = full

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
	p.NumDels += uint64(delCount)

	p.add(adds)

	return nil
}

// add adds all the passed in leaves to the accumulator.
func (p *Pollard) add(adds []Leaf) {
	for _, add := range adds {
		// Create a node from the hash. If the pollard is Full, then remember
		// every node.
		node := &polNode{data: add.Hash, remember: add.Remember}
		if p.Full {
			node.remember = true
		}

		// Add the hash to the map if this node is supposed to be remembered.
		if node.remember {
			p.NodeMap[add.mini()] = node
		}

		newRoot := p.calculateNewRoot(node)
		p.Roots = append(p.Roots, newRoot)

		// Increment as we added a leaf.
		p.NumLeaves++
	}
}

// calculateNewRoot adds the node to the accumulator and calculates the new root.
func (p *Pollard) calculateNewRoot(node *polNode) *polNode {
	// We can tell where the roots are by looking at the binary representation
	// of the NumLeaves. Wherever there's a 1, there's a root.
	//
	// NumLeaves of 8 will be '1000' in binary, so there will be one root at
	// row 3. NumLeaves of 3 will be '11' in binary, so there's two roots. One at
	// row 0 and one at row 1.
	//
	// In this loop below, we're looking for these roots by checking if there's
	// a '1'. If there is a '1', we'll hash the root being added with that root
	// until we hit a '0'.
	for h := uint8(0); (p.NumLeaves>>h)&1 == 1; h++ {
		// Grab and pop off the root that will become a node.
		// NOTE Explicitly not niling out the polNode for GC as we still need it.
		root := p.Roots[len(p.Roots)-1]
		p.Roots = p.Roots[:len(p.Roots)-1]

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

		// Check if the current node should be remembered
		if node.remember {
			// If the sibling needs to be remembered, store this node
			sibling, err := node.getSibling()
			if err == nil && sibling != nil && sibling.remember {
				p.RequiredNodes = append(p.RequiredNodes, node)
			}

			// Recursively check for aunt nodes
			p.checkAuntNodes(node)
		}

		// Calculate the hash of the new root.
		nHash := parentHash(root.data, node.data)

		newRoot := &polNode{data: nHash, lNiece: root, rNiece: node}
		if p.Full {
			newRoot.remember = true
		}

		// Set aunt.
		updateAunt(newRoot)
		newRoot.prune()
		node = newRoot
	}

	// // Print the required nodes
	// for _, requiredNode := range p.RequiredNodes {
	// 	fmt.Println(requiredNode)
	// }

	return node
}

// checkAuntNodes recursively checks for aunt nodes to remember.
func (p *Pollard) checkAuntNodes(node *polNode) {
	parent, err := node.getParent()
	if err == nil && parent != nil {
		// Check if the aunt needs to be remembered
		aunt, err := parent.getSibling()
		if err == nil && aunt != nil && aunt.remember {
			// Check if the aunt's sibling needs to be remembered
			auntSibling, err := aunt.getSibling()
			if err == nil && auntSibling != nil && auntSibling.remember {
				// Check if the aunt's nieces need to be remembered
				if aunt.lNiece != nil && aunt.lNiece.remember && aunt.rNiece != nil && aunt.rNiece.remember {
					// Store the aunt node
					p.RequiredNodes = append(p.RequiredNodes, aunt)
				}
			}
		}

		// Recursively check for aunt nodes until there are no aunt nodes
		p.checkAuntNodes(parent)
	}
}

// remove removes all the positions that are passed in.
func (p *Pollard) remove(dels []uint64) error {
	sort.Slice(dels, func(a, b int) bool { return dels[a] < dels[b] })

	totalRows := treeRows(p.NumLeaves)
	dels = deTwin(dels, totalRows)

	for _, del := range dels {
		// If a root is being deleted, then we mark it and all the leaves below
		// it to be deleted.
		if isRootPosition(del, p.NumLeaves, totalRows) {
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
	tree, _, _, err := detectOffset(del, p.NumLeaves)
	if err != nil {
		return err
	}
	if tree > uint8(len(p.Roots)-1) {
		return fmt.Errorf("getNode error: couldn't fetch %d, "+
			"calculated root index of %d but only have %d roots",
			del, tree, len(p.Roots))
	}

	// Delete from map.
	delete(p.NodeMap, p.Roots[tree].data.mini())

	if p.Roots[tree].lNiece != nil {
		p.Roots[tree].lNiece.aunt = nil
	}
	if p.Roots[tree].rNiece != nil {
		p.Roots[tree].rNiece.aunt = nil
	}
	p.Roots[tree].chop()
	p.Roots[tree].aunt = nil
	p.Roots[tree].data = empty

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
		_, found := p.NodeMap[toNode.data.mini()]
		if found {
			p.NodeMap[toNode.data.mini()] = toNode
		}
	}

	// Delete the node from the map.
	delete(p.NodeMap, fromNodeSib.data.mini())
	delNode(fromNodeSib)

	// If to position is a root, there's no parent hash to be calculated so
	// return early.
	totalRows := treeRows(p.NumLeaves)
	to := parent(del, totalRows)
	if isRootPosition(to, p.NumLeaves, totalRows) {
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
		delete(p.NodeMap, del.mini())
	}
}

// Undo reverts the most recent modify that happened to the accumulator. The passed in numAdds,
// dels and delHashes should correspond to block being un-done. prevRoots should be of the block
// that the caller is trying to go back to.
//
// Ex: If the caller is trying to go back to block 9, the numAdds, dels, and delHashes should be
// the adds and dels that happened to get to block 10. prevRoots should be the roots at block 9.
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
	if len(p.Roots) >= int(numRoots(p.NumLeaves)) {
		return nil
	}
	dels := make([]uint64, len(origDels))
	copy(dels, origDels)

	// Sort before detwining.
	sort.Slice(dels, func(a, b int) bool { return dels[a] < dels[b] })
	dels = deTwin(dels, treeRows(p.NumLeaves))

	// Copy to avoid mutating the original.
	copyRoots := make([]Hash, len(prevRoots))
	copy(copyRoots, prevRoots)

	// Add in the empty roots that was removed by the deletions to the prevRoots.
	for _, del := range dels {
		if isRootPosition(del, p.NumLeaves, treeRows(p.NumLeaves)) {
			tree, _, _, err := detectOffset(del, p.NumLeaves)
			if err != nil {
				return err
			}
			copyRoots[tree] = empty
		}
	}

	// Add empty roots that was present in the previous roots.
	for i, prevRoot := range copyRoots {
		if prevRoot == empty {
			for i >= len(p.Roots) {
				p.Roots = append(p.Roots, &polNode{remember: p.Full})
				continue
			}
			if p.Roots[i].data != empty {
				p.Roots = append(p.Roots, nil)
				copy(p.Roots[i+1:], p.Roots[i:])
				p.Roots[i] = &polNode{data: prevRoot, remember: p.Full}
			}
		}
	}

	return nil
}

// undoSingleAdd undoes one leaf that was added to the accumulator.
func (p *Pollard) undoSingleAdd() {
	lowestRootRow := getLowestRoot(p.NumLeaves)
	for row := int(lowestRootRow); row >= 0; row-- {
		lowestRoot := p.Roots[len(p.Roots)-1]
		p.Roots = p.Roots[:len(p.Roots)-1]

		lNiece, rNiece := lowestRoot.lNiece, lowestRoot.rNiece

		if lNiece != nil {
			swapNieces(lNiece, rNiece)
			lNiece.aunt, rNiece.aunt = nil, nil
			p.Roots = append(p.Roots, lNiece, rNiece)
		} else {
			row = -1
		}

		delete(p.NodeMap, lowestRoot.data.mini())
		delNode(lowestRoot)
	}
	p.NumLeaves--
}

func (p *Pollard) undoDels(dels []uint64, delHashes []Hash) error {
	if len(dels) != len(delHashes) {
		return fmt.Errorf("Got %d targets to be deleted but have %d hashes",
			len(dels), len(delHashes))
	}

	pnps := make([]nodeAndPos, len(dels))
	for i := range dels {
		pn := &polNode{data: delHashes[i], remember: p.Full}
		pnps[i] = nodeAndPos{pn, dels[i]}

		p.NodeMap[delHashes[i].mini()] = pn
	}
	sort.Slice(pnps, func(a, b int) bool { return pnps[a].pos < pnps[b].pos })

	totalRows := treeRows(p.NumLeaves)
	pnps = deTwinPolNode(pnps, totalRows)

	// Go through all the de-twined nodes and all from the highest position first.
	for i := len(pnps) - 1; i >= 0; i-- {
		pnp := pnps[i]

		if isRootPosition(pnp.pos, p.NumLeaves, treeRows(p.NumLeaves)) {
			tree, _, _, err := detectOffset(pnp.pos, p.NumLeaves)
			if err != nil {
				return err
			}
			p.Roots[tree] = pnp.node
			continue
		} else {
			err := p.undoSingleDel(pnp.node, pnp.pos)
			if err != nil {
				return err
			}
		}
	}

	p.NumDels -= uint64(len(delHashes))

	return nil
}

func (p *Pollard) undoSingleDel(node *polNode, pos uint64) error {
	totalRows := treeRows(p.NumLeaves)

	siblingPos := parent(pos, totalRows)
	sibling, aunt, _, err := p.getNode(siblingPos)
	if err != nil {
		return fmt.Errorf("Couldn't undo %s at position %d, err: %v",
			hex.EncodeToString(node.data[:]), pos, err)
	}

	pHash := calculateParentHash(pos, node, sibling)
	parent := &polNode{data: pHash, remember: p.Full}

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

		_, found := p.NodeMap[sibling.data.mini()]
		if found {
			p.NodeMap[sibling.data.mini()] = sibling
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
	roots := make([]Hash, 0, len(p.Roots))

	for _, root := range p.Roots {
		roots = append(roots, root.data)
	}

	return roots
}

// GetTotalCount returns the count of all the polNodes in the pollard.
func (p *Pollard) GetTotalCount() int64 {
	var size int64
	for _, root := range p.Roots {
		size += getCount(root)
	}

	return size
}

// SerializeSize returns how many bytes it'd take to serialize the pollard.
func (p *Pollard) SerializeSize() int {
	count := p.GetTotalCount()
	// 32 byte hashes + 8 byte NumLeaves + 8 byte NumDels +
	// 1 byte leaf-ness + 1 byte niece-ness
	return int((count * 32) + 16 + (count * 2))
}

// Write to writes all the data of the pollard to the writer.
func (p *Pollard) WriteTo(w io.Writer) (int64, error) {
	totalBytes := int64(0)

	// First write the num leaves.
	var buf [8]byte
	binary.LittleEndian.PutUint64(buf[:], p.NumLeaves)
	bytes, err := w.Write(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += int64(bytes)

	// Then write the number of dels.
	binary.LittleEndian.PutUint64(buf[:], p.NumDels)
	bytes, err = w.Write(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += int64(bytes)

	// Then write the entire pollard to the writer.
	for _, root := range p.Roots {
		bytes, err := writeOne(root, w)
		if err != nil {
			return totalBytes, err
		}

		totalBytes += bytes
	}

	return totalBytes, nil
}

func writeOne(n *polNode, w io.Writer) (int64, error) {
	totalBytes := int64(0)

	if n == nil {
		return totalBytes, nil
	}
	wroteBytes, err := w.Write(n.data[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += int64(wroteBytes)

	// Mark leaf-ness. If we don't have any children, we're a leaf.
	lChild, rChild, err := n.getChildren()
	if err != nil {
		return totalBytes, err
	}
	if lChild == nil && rChild == nil {
		wroteBytes, err := w.Write([]byte{1})
		if err != nil {
			return totalBytes, err
		}
		totalBytes += int64(wroteBytes)
	} else {
		wroteBytes, err := w.Write([]byte{0})
		if err != nil {
			return totalBytes, err
		}
		totalBytes += int64(wroteBytes)
	}

	// If nieces are present, then call writeOne on those nieces as well and
	// mark as nieces being present. If they don't exist, just mark as nieces
	// missing and move on.
	if n.lNiece != nil && n.rNiece != nil {
		wroteBytes, err := w.Write([]byte{1})
		if err != nil {
			return totalBytes, err
		}
		totalBytes += int64(wroteBytes)

		leftBytes, err := writeOne(n.lNiece, w)
		if err != nil {
			return totalBytes, err
		}
		totalBytes += leftBytes

		rightBytes, err := writeOne(n.rNiece, w)
		if err != nil {
			return totalBytes, err
		}
		totalBytes += rightBytes
	} else {
		wroteBytes, err := w.Write([]byte{0})
		if err != nil {
			return totalBytes, err
		}
		totalBytes += int64(wroteBytes)
	}

	return totalBytes, nil
}

// RestorePollardFrom restores the pollard from the reader.
func RestorePollardFrom(r io.Reader) (int64, *Pollard, error) {
	p := NewAccumulator(true)
	totalBytes := int64(0)

	// Read numleaves.
	var buf [8]byte
	readBytes, err := r.Read(buf[:])
	if err != nil {
		return totalBytes, nil, err
	}
	totalBytes += int64(readBytes)
	p.NumLeaves = binary.LittleEndian.Uint64(buf[:])

	// Read NumDels.
	readBytes, err = r.Read(buf[:])
	if err != nil {
		return totalBytes, nil, err
	}
	totalBytes += int64(readBytes)
	p.NumDels = binary.LittleEndian.Uint64(buf[:])

	// For each of the roots that we have, initialize the polnodes
	// with readOne.
	p.Roots = make([]*polNode, numRoots(p.NumLeaves))
	for i := range p.Roots {
		p.Roots[i] = new(polNode)
		readBytes, err := p.readOne(p.Roots[i], r)
		if err != nil {
			return totalBytes, nil, err
		}

		totalBytes += readBytes
	}

	// Sanity check.
	if len(p.NodeMap) != int(p.NumLeaves-p.NumDels) {
		err = fmt.Errorf("RestorePollard fail. Expect a total or %d "+
			"leaves but only have %d leaves in the map", p.NumLeaves-p.NumDels, len(p.NodeMap))
		return totalBytes, nil, err
	}

	return totalBytes, &p, nil
}

func (p *Pollard) readOne(n *polNode, r io.Reader) (int64, error) {
	totalBytes := int64(0)

	// Read from the reader. If we're at EOF, we've finished restoring
	// the pollard.
	readBytes, err := r.Read(n.data[:])
	if err != nil {
		if err == io.EOF {
			return int64(readBytes), nil
		}
		return totalBytes, err
	}
	totalBytes += int64(readBytes)

	// Read leaf-ness. If this node is a leaf, then we need to store it in
	// the map.
	var buf [1]byte
	readBytes, err = r.Read(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += int64(readBytes)
	if buf[0] == 1 {
		if n.data != empty {
			p.NodeMap[n.data.mini()] = n
		}
	}

	// Read if the node has nieces. If the node does have nieces, then we call readOne
	// for the nieces as well.
	readBytes, err = r.Read(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += int64(readBytes)

	if buf[0] == 1 {
		n.lNiece = &polNode{aunt: n}
		leftBytes, err := p.readOne(n.lNiece, r)
		if err != nil {
			return totalBytes, err
		}
		totalBytes += leftBytes

		n.rNiece = &polNode{aunt: n}
		rightBytes, err := p.readOne(n.rNiece, r)
		if err != nil {
			return totalBytes, err
		}
		totalBytes += rightBytes
	}

	return totalBytes, nil
}
