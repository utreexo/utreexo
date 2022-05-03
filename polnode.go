package utreexo

import (
	"encoding/hex"
	"fmt"
	"sort"
)

// empty is needed as go initializes an array as all 0s. Used to compare
// if read 32 byte slices were empty.
var empty [32]byte

// Hash is the 32 byte of a 256 bit hash.
type Hash [32]byte

// miniHash is the first 12 bytes of a 256 bit hash.
type miniHash [12]byte

// mini takes the first 12 slices of a Hash and outputs a miniHash.
func (h Hash) mini() (m miniHash) {
	copy(m[:], h[:12])
	return
}

// Leaf contains a hash and a hint about whether it should be cached.
type Leaf struct {
	Hash
	Remember bool
}

// polNode is a node in the pollard.
type polNode struct {
	leftNiece, rightNiece *polNode
	aunt                  *polNode
	data                  Hash
	remember              bool
}

// getSibling returns the sibling of this node.
func (n *polNode) getSibling() (*polNode, error) {
	aunt := n.aunt

	// I'm a root so I have no sibling.
	if aunt == nil {
		return nil, nil
	}

	// Get my sibling which is pointing to my children.
	var sibling *polNode
	if n == aunt.leftNiece {
		sibling = aunt.rightNiece
	} else if n == aunt.rightNiece {
		sibling = aunt.leftNiece
	} else {
		return nil, fmt.Errorf("Node with hash %s has an incorrect aunt pointer "+
			"or the aunt with hash %s has incorrect pointer to its nieces",
			hex.EncodeToString(n.data[:]), hex.EncodeToString(aunt.data[:]))
	}

	return sibling, nil
}

// getParent returns the parent of this node.
func (n *polNode) getParent() (*polNode, error) {
	aunt := n.aunt

	// I'm a root so there's no parent.
	if aunt == nil {
		return nil, nil
	}

	// My aunt is a root so my aunt is my parent. This is because roots point to their children.
	if aunt.aunt == nil {
		return aunt, nil
	}

	var parent *polNode
	if aunt.aunt.leftNiece == aunt {
		parent = aunt.aunt.rightNiece
	} else if aunt.aunt.rightNiece == aunt {
		parent = aunt.aunt.leftNiece
	} else {
		return nil, fmt.Errorf("Node with hash %s has an incorrect aunt pointer "+
			"or the aunt with hash %s has incorrect pointer to its nieces",
			hex.EncodeToString(aunt.data[:]), hex.EncodeToString(aunt.aunt.data[:]))
	}

	return parent, nil
}

// getChildren returns the children of this node.
func (n *polNode) getChildren() (*polNode, *polNode, error) {
	aunt := n.aunt

	// No aunt means that this node is a root. Roots point to their children.
	if aunt == nil {
		return n.leftNiece, n.rightNiece, nil
	}

	// Get my sibling which is pointing to my children.
	sibling, err := n.getSibling()
	if err != nil {
		return nil, nil, err
	}

	if sibling == nil {
		return nil, nil, fmt.Errorf("Node with hash %s isn't a root but doens't have a sibling",
			hex.EncodeToString(n.data[:]))
	}

	return sibling.leftNiece, sibling.rightNiece, nil
}

// getNode returns the node, it's sibling, and the parent of the given position.
func (p *Pollard) getNode(pos uint64) (n, sibling, parent *polNode, err error) {
	// Tree is the root the position is located under.
	// branchLen denotes how far down the root the position is.
	// bits tell us if we should go down to the left child or the right child.
	if pos >= maxPosition(treeRows(p.numLeaves)) {
		return nil, nil, nil,
			fmt.Errorf("Position %d does not exist in tree of %d leaves", pos, p.numLeaves)
	}
	tree, branchLen, bits, err := detectOffset(pos, p.numLeaves)
	if err != nil {
		return nil, nil, nil, err
	}
	if tree >= uint8(len(p.roots)) {
		return nil, nil, nil, fmt.Errorf("getNode error: couldn't fetch %d, "+
			"calculated root index of %d but only have %d roots",
			pos, tree, len(p.roots))
	}

	// Initialize.
	n, sibling, parent = p.roots[tree], p.roots[tree], nil

	// Go down the tree to find the node we're looking for.
	for h := int(branchLen) - 1; h >= 0; h-- {
		// Parent is the sibling of the current node as each of the
		// nodes point to their nieces.
		parent = sibling

		// Figure out which node we need to follow.
		niecePos := uint8(bits>>h) & 1
		if isLeftNiece(uint64(niecePos)) {
			n, sibling = n.leftNiece, n.rightNiece
		} else {
			n, sibling = n.rightNiece, n.leftNiece
		}

		// Return early if the path to the node we're looking for
		// doesn't exist.
		if n == nil {
			return nil, nil, nil, nil
		}
	}

	return
}

// getHash is a wrapper around getNode. Returns an empty hash if the hash for
// the given position couldn't be read.
func (p *Pollard) getHash(pos uint64) Hash {
	n, _, _, err := p.getNode(pos)
	if err != nil || n == nil {
		return empty
	}

	return n.data
}

func (p *Pollard) calculatePosition(node *polNode) uint64 {
	// Tells whether to follow the left child or the right child when going
	// down the tree. 0 means left, 1 means right.
	leftRightIndicator := uint64(0)

	polNode := node

	rowsToTop := 0
	for polNode.aunt != nil {
		if polNode.aunt.leftNiece == polNode {
			// Left
			leftRightIndicator <<= 1
		} else {
			// Right
			leftRightIndicator <<= 1
			leftRightIndicator |= 1
		}

		polNode = polNode.aunt

		// Ugly but need to flip the bit that we set in this loop as the roots
		// don't point their children instead of their nieces.
		if rowsToTop == 0 {
			leftRightIndicator ^= 1
		}
		rowsToTop++
	}
	forestRows := treeRows(p.numLeaves)

	// Calculate which row the root is on.
	rootRow := -1
	// Start from the lowest root.
	rootIdx := len(p.roots) - 1
	for h := 0; h <= int(forestRows); h++ {
		// Because every root represents a perfect tree of every leaf
		// we ever added, each root position will be a power of 2.
		//
		// Go through the bits of numLeaves. Every bit that is on
		// represents a root.
		if (p.numLeaves>>h)&1 == 1 {
			// If we found the root, save the row to rootRow
			// and return.
			if p.roots[rootIdx].data == polNode.data {
				rootRow = h
				break
			}

			// Check the next higher root.
			rootIdx--
		}
	}
	//fmt.Println("node", hex.EncodeToString(node.data[:]))
	//auntHash := "nil"
	//auntauntHash := "nil"
	//if node.aunt != nil {
	//	auntHash = hex.EncodeToString(node.aunt.data[:])
	//	fmt.Println("node.aunt", auntHash)

	//	if node.aunt.aunt != nil {
	//		auntauntHash = hex.EncodeToString(node.aunt.aunt.data[:])
	//	}
	//	fmt.Println("node.aunt.aunt", auntauntHash)
	//}

	// Start from the root and work our way down the position that we want.
	retPos := rootPosition(p.numLeaves, uint8(rootRow), forestRows)

	for i := 0; i < rowsToTop; i++ {
		isRight := uint64(1) << i
		if leftRightIndicator&isRight == isRight {
			// Grab the sibling since the pollard nodes point to their
			// niece. My sibling's nieces are my children.
			retPos = sibling(rightChild(retPos, forestRows))
		} else {
			// Grab the sibling since the pollard nodes point to their
			// niece. My sibling's nieces are my children.
			retPos = sibling(leftChild(retPos, forestRows))
		}
	}

	return retPos
}

// deadEnd returns true if both nieces are nil.
func (n *polNode) deadEnd() bool {
	return n.leftNiece == nil && n.rightNiece == nil
}

// prune prunes deadend children.
// don't prune at the bottom; use leaf prune instead at row 1
func (n *polNode) prune() {
	remember := n.leftNiece.remember || n.rightNiece.remember
	if n.leftNiece.deadEnd() && !remember {
		n.leftNiece = nil
	}
	if n.rightNiece.deadEnd() && !remember {
		n.rightNiece = nil
	}
}

// chop turns a node into a deadEnd by setting both nieces to nil.
func (n *polNode) chop() {
	n.leftNiece = nil
	n.rightNiece = nil
}

// delNode removes pointers so that this node can be garbage collected.
func delNode(node *polNode) {
	// Stop pointing to my aunt and make my aunt stop pointing at me.
	if node.aunt != nil {
		// Figure out if this node is the left or right niece and make that nil.
		if node.aunt.rightNiece == node {
			node.aunt.rightNiece = nil
		} else if node.aunt.leftNiece == node {
			node.aunt.leftNiece = nil
		} else {
			// Purposely left empty. It's ok if my aunt is not pointing
			// at me because that means it's already been updated.
		}
	}
	node.aunt = nil

	// Stop pointing to my leftNiece and make my leftNiece stop pointing at me.
	if node.leftNiece != nil {
		node.leftNiece.aunt = nil
	}
	node.leftNiece = nil

	// Same for right niece.
	if node.rightNiece != nil {
		node.rightNiece.aunt = nil
	}
	node.rightNiece = nil

	// Make myself nil.
	node = nil
}

func moveNode(from, fromSib, to, toSib *polNode) {
	//swapNieces(from, fromSib)
	//transferNiece(toSib, from)
	transferNiece(to, fromSib)

	transferAunt(from, to)
	transferNiece(from, to)
}

// swapNieces makes a's nieces become b's nieces and vise-versa.
func swapNieces(a, b *polNode) {
	a.leftNiece, a.rightNiece, b.leftNiece, b.rightNiece =
		b.leftNiece, b.rightNiece, a.leftNiece, a.rightNiece
	updateAunt(a)
	updateAunt(b)
}

// transferNiece transfers b's nieces to a.
func transferNiece(a, b *polNode) {
	a.leftNiece, a.rightNiece = b.leftNiece, b.rightNiece
	b.leftNiece, b.rightNiece = nil, nil
	updateAunt(a)
}

// transferAunt transfers b's aunt to a.
func transferAunt(a, b *polNode) error {
	// Make a's aunt stop pointing at a.
	if a.aunt != nil {
		if a.aunt.leftNiece == a {
			a.aunt.leftNiece = nil
		} else if a.aunt.rightNiece == a {
			a.aunt.rightNiece = nil
		} else {
			return fmt.Errorf("Node with hash %s has an incorrect aunt pointer "+
				"or the aunt with hash %s has incorrect pointer to its nieces",
				hex.EncodeToString(a.data[:]), hex.EncodeToString(a.aunt.data[:]))
		}
	}

	// Make b's aunt point to a instead of b.
	if b.aunt != nil {
		if b.aunt.leftNiece == b {
			b.aunt.leftNiece = a
		} else if b.aunt.rightNiece == b {
			b.aunt.rightNiece = a
		} else {
			return fmt.Errorf("Node with hash %s has an incorrect aunt pointer "+
				"or the aunt with hash %s has incorrect pointer to its nieces",
				hex.EncodeToString(b.data[:]), hex.EncodeToString(b.aunt.data[:]))
		}
	}

	// Transfer b's aunt to a.
	a.aunt = b.aunt
	if a.aunt != nil {
		updateAunt(a.aunt)
	}

	return nil
}

// updateAunt works its way down, updating the aunts for all the nieces until it
// encounters the first niece that has the correct aunt.
func updateAunt(n *polNode) {
	if n.leftNiece != nil {
		// If the aunt is correct, we can return now as all nieces
		// of this niece will have the correct aunt.
		if n.leftNiece.aunt == n {
			return
		} else {
			// Update the aunt for this niece and check the nieces of this niece.
			n.leftNiece.aunt = n
			updateAunt(n.leftNiece)
		}
	}

	// Do the same for the other niece.
	if n.rightNiece != nil {
		if n.rightNiece.aunt == n {
			return
		} else {
			n.rightNiece.aunt = n
			updateAunt(n.rightNiece)
		}
	}
}

// hashToRoot calculates the hash of the node passed in and all its ancestors
// up to the root.
func hashToRoot(node *polNode) error {
	for node != nil {
		// Grab children of this parent.
		leftChild, rightChild, err := node.getChildren()
		if err != nil {
			return err
		}
		node.data = parentHash(leftChild.data, rightChild.data)

		// Grab the next parent that needs the hash updated.
		node, err = node.getParent()
		if err != nil {
			return err
		}
	}

	return nil
}

// calculateParentHash returns the parent hash of the passed in nodes.
func calculateParentHash(nodePos uint64, node, sibling *polNode) Hash {
	if isLeftNiece(nodePos) {
		return parentHash(node.data, sibling.data)
	}
	return parentHash(sibling.data, node.data)
}

type nodeAndPos struct {
	node *polNode
	pos  uint64
}

func deTwinPolNode(polNodes []nodeAndPos, forestRows uint8) []nodeAndPos {
	for i := 0; i < len(polNodes); i++ {
		// 1: Check that there's at least 2 elements in the slice left.
		// 2: Check if the right sibling of the current element matches
		//    up with the next element in the slice.
		if i+1 < len(polNodes) && rightSib(polNodes[i].pos) == polNodes[i+1].pos {
			// Grab the position of the del.
			pn := polNodes[i]
			sibNode := polNodes[i+1].node

			swapNieces(pn.node, sibNode)

			// Remove both of the child nodes from the slice.
			// NOTE the deleted nodes will NOT be garbage collected.
			// This is done on purpose as these nodes are meant to be
			// populated into the pollard.
			polNodes = append(polNodes[:i], polNodes[i+2:]...)

			// Calculate and insert the parent in order.
			parentNode := &polNode{data: parentHash(pn.node.data, sibNode.data)}
			parentNode.leftNiece = pn.node
			parentNode.rightNiece = sibNode
			updateAunt(parentNode)

			position := parent(pn.pos, forestRows)
			polNodes = insertSortNodeAndPos(polNodes, nodeAndPos{parentNode, position})

			// Decrement one since the next element we should
			// look at is at the same index because the slice decreased
			// in length by one.
			i--
		}
	}

	return polNodes
}

func insertSortNodeAndPos(nodes []nodeAndPos, el nodeAndPos) []nodeAndPos {
	index := sort.Search(len(nodes), func(i int) bool { return nodes[i].pos > el.pos })
	nodes = append(nodes, nodeAndPos{})
	copy(nodes[index+1:], nodes[index:])
	nodes[index] = el

	return nodes
}
