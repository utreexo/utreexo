package utreexo

import (
	"encoding/binary"
	"fmt"
	"io"
	"sort"
	"sync"

	"golang.org/x/exp/slices"
)

// Assert that MapPollard implements the Utreexo interface.
var _ Utreexo = (*MapPollard)(nil)

// Node is the data for an element in the utreexo accumulator. It can be either a leaf or a node.
type Node struct {
	// Remember indicates if this node should be remembered.
	Remember bool

	// The left and right child of this node.
	LBelow, RBelow, Above Hash

	// AddIndex indicates which leaf it was at the height the leaf was added.
	// -1 if it's not available either because the node is not a leaf or if
	// the mappollard doesn't know because it's not full.
	AddIndex int32
}

// deadEnd indicates that the node doesn't have any nieces.
func (n *Node) deadEnd() bool {
	return n.LBelow == empty && n.RBelow == empty
}

// pruneable returns true if the node and the sibling doesn't need to be cached.
func (n *Node) pruneable(sib Node) (bool, error) {
	if sib.Above != n.Above {
		return false, fmt.Errorf("given sib points to %v while I point to %v",
			sib.Above, n.Above)
	}

	if sib.Remember || n.Remember {
		return false, nil
	}

	return n.deadEnd() && sib.deadEnd(), nil
}

// getSibHash takes in a below node's hash and returns its sibhash.
func (n *Node) getSibHash(hash Hash) (Hash, bool, error) {
	// Grab sibling.
	if hash == n.LBelow {
		return n.RBelow, false, nil
	} else if hash == n.RBelow {
		return n.LBelow, true, nil
	} else {
		return empty, false, fmt.Errorf("above node for hash %v points to left %v and right %v",
			hash, n.LBelow, n.RBelow)
	}
}

// isRoot returns true if the node doesn't point to any above nodes.
func (n *Node) isRoot() bool {
	return n.Above == empty
}

// String returns a human-readable string of the node.
func (n *Node) String() string {
	return fmt.Sprintf("rememeber %v, above %v, l %v, r %v, addIndex %v",
		n.Remember, n.Above, n.LBelow, n.RBelow, n.AddIndex)
}

// view is a view of the mappollard. After the deletion, the nodes and roots will be modified and the
// deleted nodes' keys will be included in the removed slice.
type view struct {
	// Shared data.
	roots []Hash
	nodes map[Hash]Node

	// Data for removing.
	removed []Hash

	// Data for adding.
	numLeaves uint64
	totalRows uint8
	full      bool
}

// initView returns an initialized view.
func initView(rs []Hash, count int) *view {
	r := make([]Hash, len(rs))
	copy(r, rs)
	return &view{
		roots:   r,
		nodes:   make(map[Hash]Node),
		removed: make([]Hash, 0, count),
	}
}

// del removes the key from the nodes map and adds that hash to the removed slice.
func (v *view) del(hash Hash) {
	delete(v.nodes, hash)
	v.removed = append(v.removed, hash)
}

// fetchNodeForDel fetches all the nodes that are needed to remove the given hash.
func (v *view) fetchNodeForDel(hash Hash) (
	node, sibNode, aNode Node, sibHash Hash, foundNode bool, err error) {

	node, foundNode = v.nodes[hash]
	if !foundNode {
		return
	}

	if node.isRoot() {
		return
	}

	var found bool
	aNode, found = v.nodes[node.Above]
	if !found {
		err = fmt.Errorf("fetchNodeForDel err: node %v points to above of %v but wasn't found",
			hash, node.Above)
		return
	}

	sibHash, _, err = aNode.getSibHash(hash)
	if err != nil {
		return
	}

	sibNode, found = v.nodes[sibHash]
	if !found {
		err = fmt.Errorf("node %v has l %v, r %v but %v wasn't found",
			node.Above, node.LBelow, node.RBelow, sibHash)
		return
	}

	return
}

// removeNode deletes the hash and all its below nodes.
func (v *view) removeNode(hash Hash, node Node) error {
	v.del(hash)

	if node.isRoot() {
		// write the zombie root in the roots slice.
		idx := slices.Index(v.roots, hash)
		if idx == -1 {
			return fmt.Errorf("couldn't find root of %v in the roots slice", hash)
		}
		v.roots[idx] = empty
	}

	if node.LBelow != empty {
		lNode, found := v.nodes[node.LBelow]
		if !found {
			return nil
		}

		v.removeNode(node.LBelow, lNode)
	}

	if node.RBelow != empty {
		rNode, found := v.nodes[node.RBelow]
		if !found {
			return nil
		}

		v.removeNode(node.RBelow, rNode)
	}

	return nil
}

// updateAbove updates n's belows to point above to the newHash.
func (v *view) updateAbove(n Node, newHash Hash) error {
	if n.LBelow == empty {
		return nil
	}

	lBelow, lfound := v.nodes[n.LBelow]
	rBelow, rfound := v.nodes[n.RBelow]
	if !lfound && !rfound {
		return nil
	}

	if !lfound || !rfound {
		return fmt.Errorf("n points to lBelow of %v and rBelow of %v "+
			"but only one of them exists", n.LBelow, n.RBelow)
	}

	lBelow.Above = newHash
	rBelow.Above = newHash

	v.nodes[n.LBelow] = lBelow
	v.nodes[n.RBelow] = rBelow

	return nil
}

// swapBelow swaps the below nodes of a and b.
func (v *view) swapBelow(a, b Node, aHash, bHash Hash) (Node, Node, error) {
	err := v.updateAbove(a, bHash)
	if err != nil {
		return a, b, err
	}
	err = v.updateAbove(b, aHash)
	if err != nil {
		return a, b, err
	}

	// Swap below nodes.
	a.LBelow, a.RBelow, b.LBelow, b.RBelow =
		b.LBelow, b.RBelow, a.LBelow, a.RBelow

	return a, b, err
}

// a gives its below nodes to b.
func (v *view) giveBelow(a, b Node, bHash Hash) (Node, Node, error) {
	err := v.updateAbove(a, bHash)
	if err != nil {
		return a, b, err
	}

	b.LBelow, b.RBelow = a.LBelow, a.RBelow
	a.LBelow, a.RBelow = empty, empty
	return a, b, nil
}

// setAsSib sets the newSib as the node's sibling.
func (v *view) setAsSib(node, newSib Node, nodeHash, newSibHash Hash) (Node, Node, error) {
	// Get above node.
	aNode, found := v.nodes[node.Above]
	if !found {
		return node, newSib, fmt.Errorf("setAsSib err: node %v points to above of %v but wasn't found",
			nodeHash, node.Above)
	}

	// Get the current sib of node.
	curSibHash, isLeft, err := aNode.getSibHash(nodeHash)
	if err != nil {
		return node, newSib, err
	}
	curSib, found := v.nodes[curSibHash]
	if !found {
		return node, newSib, fmt.Errorf("node %v has l %v, r %v but %v wasn't found",
			node.Above, aNode.LBelow, aNode.RBelow, curSibHash)
	}

	// Node needs to point to the newSib's nieces.
	newSib, node, err = v.giveBelow(newSib, node, nodeHash)
	if err != nil {
		return node, newSib, err
	}

	// Get belows from the current sib.
	_, newSib, err = v.giveBelow(curSib, newSib, newSibHash)
	if err != nil {
		return node, newSib, err
	}

	// Set aNode to point to the new sib.
	if isLeft {
		aNode.LBelow = newSibHash
	} else {
		aNode.RBelow = newSibHash
	}

	// The new sib also need to point to the above node.
	newSib.Above = node.Above

	// Update all the nodes.
	v.del(curSibHash)
	v.nodes[nodeHash] = node
	v.nodes[newSibHash] = newSib
	v.nodes[node.Above] = aNode

	return node, newSib, nil
}

// maybeForget checks to see if the hash can be pruned from the accumulator. If it can, it prunes
// it and recursively calls itself again to see if the above node can be forgotten as well.
func (v *view) maybeForget(hash Hash) error {
	n, found := v.nodes[hash]
	if !found {
		return nil
	}

	var canPrune bool
	if n.LBelow == empty && n.RBelow == empty {
		canPrune = true
	} else {
		l, found := v.nodes[n.LBelow]
		if !found {
			return fmt.Errorf("%v points to %v but not found", hash, n.LBelow)
		}
		r, found := v.nodes[n.RBelow]
		if !found {
			return fmt.Errorf("%v points to %v but not found", hash, n.RBelow)
		}

		var err error
		canPrune, err = l.pruneable(r)
		if err != nil {
			return err
		}
	}

	if canPrune {
		v.del(n.LBelow)
		v.del(n.RBelow)

		n.LBelow = empty
		n.RBelow = empty
		v.nodes[hash] = n

		if n.Above != empty {
			err := v.maybeForget(n.Above)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

// deleteNode removes the given hash and all its children and moves its sibling up.
func (v *view) deleteNode(hash Hash) error {
	node, sibNode, aNode, sibHash, found, err := v.fetchNodeForDel(hash)
	if err != nil {
		return err
	}

	if !found {
		// It may not be cached. Nothing to do then.
		return nil
	}

	if node.isRoot() {
		return v.removeNode(hash, node)
	}

	// Swap below nodes.
	node, sibNode, err = v.swapBelow(node, sibNode, hash, sibHash)
	if err != nil {
		return err
	}
	v.removeNode(hash, node)

	// Sib becomes the root.
	if aNode.isRoot() {
		v.del(node.Above)

		idx := slices.Index(v.roots, node.Above)
		if idx == -1 {
			return fmt.Errorf("couldn't find root of %v in the roots slice", hash)
		}

		// Set sibling as the root.
		v.roots[idx] = sibHash
		sibNode.Above = empty
		v.nodes[sibHash] = sibNode

		return nil
	}

	// Move up the sibling.
	aNode, sibNode, err = v.setAsSib(aNode, sibNode, node.Above, sibHash)
	if err != nil {
		return err
	}

	// Check if the sibling is prunable.
	canPrune, err := sibNode.pruneable(aNode)
	if err != nil {
		return err
	}

	if canPrune {
		gpNode, found := v.nodes[aNode.Above]
		if !found {
			return fmt.Errorf("above node of %v not found for %v", aNode.Above, node.Above)
		}

		v.del(node.Above)
		v.del(sibHash)

		gpNode.LBelow = empty
		gpNode.RBelow = empty
		v.nodes[aNode.Above] = gpNode

		if gpNode.Above != empty {
			err = v.maybeForget(gpNode.Above)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

// updateHash updates the below and above nodes to point to the new hash and re-inserts
// the node with the new hash.
func (v *view) updateHash(before, after Hash) error {
	node, found := v.nodes[before]
	if !found {
		return nil
	}

	// Check if it's a root.
	if node.Above == empty {
		idx := slices.Index(v.roots, before)
		if idx == -1 {
			return fmt.Errorf("node %v doesn't have above but is "+
				"not in roots: %v", node, v.roots)
		}
		v.roots[idx] = after
	}

	v.del(before)
	v.nodes[after] = node

	if node.Above != empty {
		above, found := v.nodes[node.Above]
		if !found {
			return fmt.Errorf("node %v points to %v but is "+
				"not found", before, node.Above)
		}

		if above.LBelow == before {
			above.LBelow = after
		} else if above.RBelow == before {
			above.RBelow = after
		} else {
			return fmt.Errorf("updateHash above node for hash %v points to left %v and right %v",
				before, above.LBelow, above.RBelow)
		}

		v.nodes[node.Above] = above
	}

	if node.LBelow != empty {
		lBelow, found := v.nodes[node.LBelow]
		if !found {
			return fmt.Errorf("node %v points to %v but is "+
				"not found", before, node.LBelow)
		}
		lBelow.Above = after

		v.nodes[node.LBelow] = lBelow
	}

	if node.RBelow != empty {
		rBelow, found := v.nodes[node.RBelow]
		if !found {
			return fmt.Errorf("node %v points to %v but is "+
				"not found", before, node.RBelow)
		}
		rBelow.Above = after

		v.nodes[node.RBelow] = rBelow
	}

	return nil
}

// remove removes deleted leaves and updates the nodes to their new hashes after the deletion of
// the leaves.
func (v *view) remove(ins modifyInstruction) error {
	for i, afterHash := range ins.after {
		beforeHash := ins.before[i]

		if afterHash == empty {
			err := v.deleteNode(beforeHash)
			if err != nil {
				return err
			}
		} else {
			err := v.updateHash(beforeHash, afterHash)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

// add adds all the passed in leaves to the view.
func (v *view) add(adds []Leaf) error {
	for i, add := range adds {
		// Add to the accumulator.
		err := v.addSingle(add, i)
		if err != nil {
			return err
		}

		v.numLeaves++
	}

	return nil
}

// addSingle adds one leaf to the accumulator view.  If the remember field is set to true, the leaf
// will be cached.
func (v *view) addSingle(add Leaf, index int) error {
	if TreeRows(v.numLeaves+1) > v.totalRows {
		v.totalRows++
	}

	// If the map pollard is configured to be full, override the remember value in the leaf.
	if v.full {
		add.Remember = true
	}

	addHash := add.Hash
	addNode := Node{Remember: add.Remember, AddIndex: int32(index)}
	v.nodes[add.Hash] = addNode

	for h := uint8(0); (v.numLeaves>>h)&1 == 1; h++ {
		// Grab and pop off the root that will become a node.
		var root Hash
		root, v.roots = v.roots[len(v.roots)-1], v.roots[:len(v.roots)-1]

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
			continue
		}

		// Get the root we're destroying.
		curRootNode, found := v.nodes[root]
		if !found {
			return fmt.Errorf("root node %v not found", root)
		}

		// Make parent node.
		pNode := Node{LBelow: root, RBelow: addHash, AddIndex: -1, Remember: v.full}
		parentHash := parentHash(root, addHash)

		var err error
		curRootNode, addNode, err = v.swapBelow(curRootNode, addNode, root, addHash)
		if err != nil {
			return err
		}

		// Point to aunt or parent.
		addNode.Above = parentHash
		curRootNode.Above = parentHash

		// Update the nodes.
		v.nodes[addHash] = addNode
		v.nodes[root] = curRootNode

		// Prune if we can. The error only happens when both of the nodes do not point
		// to the same parent.
		canPrune, _ := addNode.pruneable(curRootNode)
		if canPrune {
			v.del(addHash)
			v.del(root)

			pNode.LBelow = empty
			pNode.RBelow = empty
		}
		v.nodes[parentHash] = pNode

		// Set the parent as the root being added for the next potential loop.
		addHash = parentHash
		addNode = pNode
	}

	v.roots = append(v.roots, addHash)

	return nil
}

// undoDeletion undo-es all the deletions that are passed in. The deletions that happened
// should be done in a single modify.
func (v *view) undoDeletion(createIndex []int32, undoInfo undoInfo, ingestIns ingestInstruction, delHashes []Hash) error {
	for undoInfo.length() > 0 {
		updateHashInfo, insertDelInfo := undoInfo.pop()
		if updateHashInfo != nil {
			if updateHashInfo.isRoot {
				tree, _, _, err := DetectOffset(updateHashInfo.rootPos, v.numLeaves)
				if err != nil {
					return err
				}

				if v.roots[tree] != empty {
					return fmt.Errorf("expected to find empty root at pos %v but got %v",
						updateHashInfo.rootPos, v.roots[tree])
				}
				v.roots[tree] = updateHashInfo.origHash
				rootNode := Node{Remember: v.full, AddIndex: -1}
				v.nodes[updateHashInfo.origHash] = rootNode
			} else {
				err := v.updateHash(updateHashInfo.curHash, updateHashInfo.origHash)
				if err != nil {
					return err
				}
			}
		} else {
			prevSibNode, curSib, aNode, curSibHash, found, err := v.fetchNodeForDel(insertDelInfo.sibHash)
			if err != nil {
				return err
			}
			if !found {
				continue
			}

			pNode := Node{Remember: v.full, Above: prevSibNode.Above, AddIndex: -1}

			if prevSibNode.isRoot() {
				idx := slices.Index(v.roots, insertDelInfo.sibHash)
				if idx == -1 {
					return fmt.Errorf("prevSib of %v is a root but is not found in roots",
						insertDelInfo.sibHash)
				}

				v.roots[idx] = insertDelInfo.pHash

				prevHashNode := Node{
					Remember: v.full,
					Above:    insertDelInfo.pHash,
					AddIndex: -1,
				}
				prevSibNode, prevHashNode, err = v.giveBelow(prevSibNode, prevHashNode, insertDelInfo.prevHash)
				if err != nil {
					return err
				}
				prevSibNode.Above = insertDelInfo.pHash

				if insertDelInfo.isLeft {
					pNode.LBelow = insertDelInfo.prevHash
					pNode.RBelow = insertDelInfo.sibHash
				} else {
					pNode.LBelow = insertDelInfo.sibHash
					pNode.RBelow = insertDelInfo.prevHash
				}

				v.nodes[insertDelInfo.pHash] = pNode
				v.nodes[insertDelInfo.sibHash] = prevSibNode
				v.nodes[insertDelInfo.prevHash] = prevHashNode
				continue
			}

			// Move the prevSibNode down.
			prevSibNode, pNode, err = v.giveBelow(prevSibNode, pNode, insertDelInfo.pHash)
			if err != nil {
				return err
			}
			prevSibNode.Above = curSibHash

			if aNode.LBelow == insertDelInfo.sibHash {
				aNode.LBelow = insertDelInfo.pHash
			} else if aNode.RBelow == insertDelInfo.sibHash {
				aNode.RBelow = insertDelInfo.pHash
			} else {
				return fmt.Errorf("%v not found. aNode %v points to l %v, r %v",
					insertDelInfo.sibHash, curSib.Above, aNode.LBelow, aNode.RBelow)
			}

			prevHashNode := Node{
				Remember: v.full,
				Above:    curSibHash,
				AddIndex: -1,
			}
			curSib, prevHashNode, err = v.giveBelow(curSib, prevHashNode, insertDelInfo.prevHash)
			if err != nil {
				return err
			}

			if insertDelInfo.isLeft {
				curSib.LBelow = insertDelInfo.prevHash
				curSib.RBelow = insertDelInfo.sibHash
			} else {
				curSib.LBelow = insertDelInfo.sibHash
				curSib.RBelow = insertDelInfo.prevHash
			}

			v.nodes[pNode.Above] = aNode
			v.nodes[curSibHash] = curSib
			v.nodes[insertDelInfo.pHash] = pNode
			v.nodes[insertDelInfo.sibHash] = prevSibNode
			v.nodes[insertDelInfo.prevHash] = prevHashNode
		}
	}

	err := v.ingest(ingestIns)
	if err != nil {
		return err
	}

	for i, index := range createIndex {
		hash := delHashes[i]
		node, found := v.nodes[hash]
		if !found {
			return fmt.Errorf("expected to find %v but didn't", hash)
		}

		node.AddIndex = int32(index)
		node.Remember = true // We probably want to hold onto these if we're adding the index.
		v.nodes[hash] = node
	}

	for hash, n := range v.nodes {
		if n.isRoot() {
			continue
		}

		aNode, found := v.nodes[n.Above]
		if !found {
			return fmt.Errorf("%v's above of %v not found", hash, n.Above)
		}

		sibHash, _, err := aNode.getSibHash(hash)
		if err != nil {
			return err
		}

		sibNode, found := v.nodes[sibHash]
		if !found {
			return fmt.Errorf("%v's belows are l %v, and r %v but %v not found",
				n.Above, aNode.LBelow, aNode.RBelow, sibHash)
		}

		// Check if the sibling is prunable.
		canPrune, err := sibNode.pruneable(n)
		if err != nil {
			return err
		}

		if canPrune {
			v.del(hash)
			v.del(sibHash)

			aNode.LBelow = empty
			aNode.RBelow = empty
			v.nodes[n.Above] = aNode

			if !aNode.isRoot() {
				err = v.maybeForget(n.Above)
				if err != nil {
					return err
				}
			}
		}
	}

	return nil
}

// ingest places the proof in the view.
func (v *view) ingest(ins ingestInstruction) error {
	if len(ins.Hashes)%3 != 0 {
		return fmt.Errorf("ingest hash length of %v is malformed as "+
			"it's not divisible by 3", len(ins.Hashes))
	}

	for i := len(ins.Hashes) - 1; i >= 0; i-- {
		hash := ins.Hashes[i]
		rBelow := ins.Hashes[i-1]
		lBelow := ins.Hashes[i-2]
		rRem := ins.isLeaf[i-1]
		lRem := ins.isLeaf[i-2]

		node, found := v.nodes[hash]
		if !found {
			return fmt.Errorf("node hash %v not found", hash)
		}

		if node.RBelow != empty {
			i--
			i--
			continue
		}

		node.LBelow = lBelow
		node.RBelow = rBelow
		v.nodes[hash] = node

		rNode := Node{
			Remember: rRem || v.full,
			Above:    hash,
			AddIndex: -1,
		}
		v.nodes[rBelow] = rNode

		lNode := Node{
			Remember: lRem || v.full,
			Above:    hash,
			AddIndex: -1,
		}
		v.nodes[lBelow] = lNode

		i--
		i--
	}

	return nil
}

// fetchNodesNeededForUndoDel fetches all the nodes that would need to be accessed to perform an
// undo of a deletion.
func (v *view) fetchNodesNeededForUndoDel(m *MapPollard, uInfo undoInfo) error {
	for i, updateHashInfo := range uInfo.updateHashInfos {
		insertDelInfo := uInfo.insertDelInfos[i]

		if updateHashInfo != nil {
			if updateHashInfo.curHash == empty {
				continue
			}
			node, found := v.fetchAndCacheNode(m, updateHashInfo.curHash)
			if !found {
				continue
			}
			if !node.isRoot() {
				aNode, found := v.fetchAndCacheNode(m, node.Above)
				if !found {
					return fmt.Errorf("getView err: node %v points to "+
						"above of %v but wasn't found",
						updateHashInfo.curHash, node.Above)
				}
				sibHash, _, err := aNode.getSibHash(updateHashInfo.curHash)
				if err != nil {
					return err
				}

				sibNode, found := v.fetchAndCacheNode(m, sibHash)
				if !found {
					return fmt.Errorf("node %v has l %v, r %v but %v wasn't found",
						node.Above, node.LBelow, node.RBelow, sibHash)
				}

				err = v.cacheBelows(m, sibNode)
				if err != nil {
					return err
				}
			}

			err := v.cacheBelows(m, node)
			if err != nil {
				return err
			}

			continue
		}

		node, found := v.fetchAndCacheNode(m, insertDelInfo.sibHash)
		if !found {
			continue
		}
		err := v.cacheBelows(m, node)
		if err != nil {
			return err
		}

		if node.isRoot() {
			continue
		}

		aNode, found := v.fetchAndCacheNode(m, node.Above)
		if !found {
			return fmt.Errorf("getView err: node %v points to above of %v but wasn't found",
				insertDelInfo.sibHash, node.Above)
		}

		sibHash, _, err := aNode.getSibHash(insertDelInfo.sibHash)
		if err != nil {
			return err
		}

		sibNode, found := v.fetchAndCacheNode(m, sibHash)
		if !found {
			return fmt.Errorf("node %v has l %v, r %v but %v wasn't found",
				node.Above, node.LBelow, node.RBelow, sibHash)
		}

		err = v.cacheBelows(m, sibNode)
		if err != nil {
			return err
		}
	}

	return nil
}

// fetchNodesNeededForAdd fetches all the nodes that would be accessed during an addition.
// This is all the root nodes & their belows.
func (v *view) fetchNodesNeededForAdd(m *MapPollard) error {
	for _, root := range m.Roots {
		if root == empty {
			continue
		}

		node, found := v.fetchAndCacheNode(m, root)
		if !found {
			return fmt.Errorf("root node of %v not found", root)
		}

		err := v.cacheBelows(m, node)
		if err != nil {
			return err
		}
	}

	return nil
}

// fetchNodesNeededForDels fetches all the nodes that would be accessed during the deletion
// based on the modifyInstruction.
func (v *view) fetchNodesNeededForDels(m *MapPollard, ins modifyInstruction) error {
	for i, beforeHash := range ins.before {
		afterHash := ins.after[i]

		if afterHash == empty {
			node, found := v.fetchAndCacheNode(m, beforeHash)
			if !found {
				continue
			}
			err := v.cacheBelows(m, node)
			if err != nil {
				return err
			}

			if node.isRoot() {
				continue
			}

			aNode, found := v.fetchAndCacheNode(m, node.Above)
			if !found {
				return fmt.Errorf("getView err: node %v points to above of %v but wasn't found",
					beforeHash, node.Above)
			}

			sibHash, _, err := aNode.getSibHash(beforeHash)
			if err != nil {
				return err
			}

			_, found = v.fetchAndCacheNode(m, sibHash)
			if !found {
				return fmt.Errorf("node %v has l %v, r %v but %v wasn't found",
					node.Above, node.LBelow, node.RBelow, sibHash)
			}

			if aNode.isRoot() {
				continue
			}

			gpNode, found := v.fetchAndCacheNode(m, aNode.Above)
			if !found {
				return fmt.Errorf("getView err: node %v points to above of %v but wasn't found",
					node.Above, aNode.Above)
			}

			aNodeSibHash, _, err := gpNode.getSibHash(node.Above)
			if err != nil {
				return err
			}

			_, found = v.fetchAndCacheNode(m, aNodeSibHash)
			if !found {
				return fmt.Errorf("node %v has l %v, r %v but %v wasn't found",
					aNode.Above, aNode.LBelow, aNode.RBelow, aNodeSibHash)
			}

			if m.Full {
				continue
			}

			// Fetch til we hit the root.
			n := gpNode
			for !n.isRoot() {
				nHash := n.Above
				n, found = v.fetchAndCacheNode(m, n.Above)
				if !found {
					return fmt.Errorf("above node of %v not found for %v", aNode.Above, nHash)
				}
			}
		} else {
			node, found := v.fetchAndCacheNode(m, beforeHash)
			if !found {
				continue
			}

			if !node.isRoot() {
				_, found := v.fetchAndCacheNode(m, node.Above)
				if !found {
					return fmt.Errorf("getView err: node %v points to "+
						"above of %v but wasn't found",
						beforeHash, node.Above)
				}
			}

			err := v.cacheBelows(m, node)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

// fetchAndCacheNode fetches and caches the node for the given hash. Caller should check that
// the given hash isn't empty as it'll just return as not found.
func (v *view) fetchAndCacheNode(m *MapPollard, hash Hash) (Node, bool) {
	node, found := m.Nodes.Get(hash)
	if !found {
		return Node{}, found
	}
	v.nodes[hash] = node

	return node, found
}

// cacheNieces will get and cache the belows of the node from the map.
func (v *view) cacheBelows(m *MapPollard, node Node) error {
	if (node.LBelow != empty) != (node.RBelow != empty) {
		return fmt.Errorf("lBelow %v rBelow %v. They should both be empty or not empty",
			node.LBelow, node.RBelow)
	}

	if node.LBelow != empty {
		lBelow, found := m.Nodes.Get(node.LBelow)
		if !found {
			return fmt.Errorf("node %v points to %v but is "+
				"not found", node, node.LBelow)
		}

		v.nodes[node.LBelow] = lBelow
	}

	if node.RBelow != empty {
		rBelow, found := m.Nodes.Get(node.RBelow)
		if !found {
			return fmt.Errorf("node %v points to %v but is "+
				"not found", node, node.RBelow)
		}

		v.nodes[node.RBelow] = rBelow
	}

	return nil
}

// getViewForUndo returns a view that is able to perform undos.
//
// NOTE: it's only capable of undoing deletions for now.
func (m *MapPollard) getViewForUndo(undoIns undoInfo) (*view, error) {
	view := initView(m.Roots, undoIns.length())
	view.numLeaves = m.NumLeaves
	view.totalRows = m.TotalRows
	view.full = m.Full

	err := view.fetchNodesNeededForUndoDel(m, undoIns)
	if err != nil {
		return nil, err
	}

	return view, nil
}

// getView returns a view that has all the necesssary information to perform a modification.
func (m *MapPollard) getView(ins modifyInstruction) (*view, error) {
	view := initView(m.Roots, len(ins.after))
	view.numLeaves = m.NumLeaves
	view.totalRows = m.TotalRows
	view.full = m.Full

	err := view.fetchNodesNeededForDels(m, ins)
	if err != nil {
		return nil, err
	}

	err = view.fetchNodesNeededForAdd(m)
	if err != nil {
		return nil, err
	}

	return view, nil
}

// commitView commits the view to the map pollard.
func (m *MapPollard) commitView(v *view) {
	for _, delHash := range v.removed {
		m.Nodes.Delete(delHash)
	}

	for k, v := range v.nodes {
		m.Nodes.Put(k, v)
	}

	m.Roots = v.roots
	m.NumLeaves = v.numLeaves
	m.TotalRows = v.totalRows
}

// NodesInterface models the interface for the data storage for the map pollard.
type NodesInterface interface {
	// Get returns the Node and a boolean to indicate if it was found or not.
	Get(Hash) (Node, bool)

	// Put puts the given hash and Node.
	Put(Hash, Node)

	// Delete removes the given hash.
	Delete(Hash)

	// Length returns the count of all the elements.
	Length() int

	// ForEach iterates through all the elements saved and calls the passed in
	// function for each one of them.
	ForEach(func(Hash, Node) error) error
}

var _ NodesInterface = (*NodesMap)(nil)

// NodesMap implements the NodesInterface interface. It's really just a map.
type NodesMap struct {
	m map[Hash]Node
}

// Get returns the data from the underlying map.
func (m *NodesMap) Get(k Hash) (Node, bool) {
	val, found := m.m[k]
	return val, found
}

// Put puts the given data to the underlying map.
func (m *NodesMap) Put(k Hash, v Node) {
	m.m[k] = v
}

// Delete removes the given key from the underlying map. No-op if the key
// doesn't exist.
func (m *NodesMap) Delete(k Hash) {
	delete(m.m, k)
}

// Length returns the amount of items in the underlying map.
func (m *NodesMap) Length() int {
	return len(m.m)
}

// ForEach calls the given function for each of the elements in the underlying map.
func (m *NodesMap) ForEach(fn func(Hash, Node) error) error {
	for k, v := range m.m {
		err := fn(k, v)
		if err != nil {
			return err
		}
	}

	return nil
}

// newNodesMap returns a pointer to a initialized map.
func newNodesMap(prealloc int) *NodesMap {
	return &NodesMap{m: make(map[Hash]Node, prealloc)}
}

// MapPollard is an implementation of the utreexo accumulators that supports pollard
// functionality.
type MapPollard struct {
	// rwLock protects the below maps from concurrent accesses.
	rwLock *sync.RWMutex

	// Roots are the tops of each of the merkle trees.
	Roots []Hash

	// Nodes are all the elements in the utreexo accumulator.
	Nodes NodesInterface

	// NumLeaves are the number of total additions that have happened in the
	// accumulator.
	NumLeaves uint64

	// TotalRows is the number of rows the accumulator has allocated for.
	TotalRows uint8

	// Full marks all the added leaves to be remembered if set to true.
	Full bool
}

// NewMapPollard returns a MapPollard with the nodes map initialized. Passing the
// full boolean as true will make the map pollard cache all leaves.
//
// NOTE: The default total rows is set to 63. This avoids costly remapping.
// For printing out the pollard for debugging purposes, set TotalRows 0 for
// pretty printing.
func NewMapPollard(full bool) MapPollard {
	return MapPollard{
		rwLock: new(sync.RWMutex),
		Nodes:  newNodesMap(0),
		Full:   full,
	}
}

// Modify takes in the additions and deletions and updates the accumulator accordingly.
func (m *MapPollard) Modify(adds []Leaf, delHashes []Hash, proof Proof) error {
	m.rwLock.Lock()
	defer m.rwLock.Unlock()

	ins, err := generateModifyIns(m.NumLeaves, delHashes, proof)
	if err != nil {
		return err
	}

	view, err := m.getView(ins)
	if err != nil {
		return err
	}
	err = view.remove(ins)
	if err != nil {
		return err
	}

	err = view.add(adds)
	if err != nil {
		return err
	}

	m.commitView(view)

	return nil
}

// ModifyAndReturnTTLs takes in the additions and deletions and updates the accumulator accordingly.
// It returns the created indexes of the deleted leaves. The the index returns as -1 if the leaves
// were added with ingest or if they were a result of and Undo without the ttls being provided.
func (m *MapPollard) ModifyAndReturnTTLs(adds []Leaf, delHashes []Hash, proof Proof) (
	[]int32, error) {

	m.rwLock.Lock()
	defer m.rwLock.Unlock()

	createIndexes := make([]int32, 0, len(delHashes))
	for _, delHash := range delHashes {
		leafInfo, found := m.Nodes.Get(delHash)
		if !found {
			return nil, fmt.Errorf("missing %v in the nodes. Cannot return ttls", delHash)
		}
		createIndexes = append(createIndexes, leafInfo.AddIndex)
	}

	ins, err := generateModifyIns(m.NumLeaves, delHashes, proof)
	if err != nil {
		return nil, err
	}

	view, err := m.getView(ins)
	if err != nil {
		return nil, err
	}
	err = view.remove(ins)
	if err != nil {
		return nil, err
	}

	err = view.add(adds)
	if err != nil {
		return nil, err
	}

	m.commitView(view)

	return createIndexes, nil
}

// String prints out the whole thing. Only viable for forest that have height of 5 and less.
func (m *MapPollard) String() string {
	return String(m)
}

// AllSubTreesToString returns a string of all the individual subtrees in the accumulator.
func (m *MapPollard) AllSubTreesToString() string {
	return AllSubTreesToString(m)
}

// undoSingleAdd undo-s the last single addition and will put back empty roots that were
// written over.
func (m *MapPollard) undoSingleAdd(prevRoots []Hash) error {
	startIdx := 0
	for i, root := range m.Roots {
		if i > len(prevRoots)-1 {
			break
		}

		if root != prevRoots[i] {
			break
		}

		startIdx++
	}

	// Pop from the root hashes and remove node.
	var rootHash Hash
	rootHash, m.Roots = m.Roots[len(m.Roots)-1], m.Roots[:len(m.Roots)-1]
	node, found := m.Nodes.Get(rootHash)
	if !found {
		return fmt.Errorf("roothash of %v not found in nodes", rootHash)
	}
	m.Nodes.Delete(rootHash)

	for i := startIdx; i < len(prevRoots); i++ {
		if prevRoots[i] == empty {
			m.Roots = append(m.Roots, prevRoots[i])
			m.Nodes.Put(prevRoots[i], Node{AddIndex: -1})

			continue
		}

		// We have nothing cached.
		if node.RBelow == empty && node.LBelow == empty {
			m.Roots = append(m.Roots, prevRoots[i])
			m.Nodes.Put(prevRoots[i], Node{AddIndex: -1})

			node = Node{AddIndex: -1}
			rootHash = empty
			continue
		}

		rNode, found := m.Nodes.Get(node.RBelow)
		if !found {
			return fmt.Errorf("rBelow of %v for %v not found in nodes",
				node.RBelow, rootHash)
		}
		lNode, found := m.Nodes.Get(node.LBelow)
		if !found {
			return fmt.Errorf("lBelow of %v for %v not found in nodes",
				node.LBelow, rootHash)
		}

		// Swap and point to children.
		var err error
		rNode, lNode, err = m.swapBelow(rNode, lNode, node.RBelow, node.LBelow)
		if err != nil {
			return err
		}

		// Make lnode the root.
		lNode.Above = empty
		m.Nodes.Put(node.LBelow, lNode)
		m.Roots = append(m.Roots, node.LBelow)

		// Remove rnode.
		m.Nodes.Delete(node.RBelow)

		// Set rNode as next node to be removed.
		rootHash = node.RBelow
		node = rNode
	}

	m.NumLeaves--
	m.TotalRows = TreeRows(m.NumLeaves)

	return nil
}

// updateAbove makes n's belows point to newHash.
func (m *MapPollard) updateAbove(n Node, newHash Hash) error {
	if n.LBelow == empty {
		return nil
	}

	lBelow, lfound := m.Nodes.Get(n.LBelow)
	rBelow, rfound := m.Nodes.Get(n.RBelow)
	if !lfound && !rfound {
		return nil
	}

	if !lfound || !rfound {
		return fmt.Errorf("n points to lBelow of %v and rBelow of %v "+
			"but only one of them exists", n.LBelow, n.RBelow)
	}

	lBelow.Above = newHash
	rBelow.Above = newHash

	m.Nodes.Put(n.LBelow, lBelow)
	m.Nodes.Put(n.RBelow, rBelow)

	return nil
}

func (m *MapPollard) swapBelow(a, b Node, aHash, bHash Hash) (Node, Node, error) {
	err := m.updateAbove(a, bHash)
	if err != nil {
		return a, b, err
	}
	err = m.updateAbove(b, aHash)
	if err != nil {
		return a, b, err
	}

	// Swap below nodes.
	a.LBelow, a.RBelow, b.LBelow, b.RBelow =
		b.LBelow, b.RBelow, a.LBelow, a.RBelow

	return a, b, err
}

// getSingleRoots returns the roots after each single addition.
func getSingleRoots(s Stump, adds []Hash) ([][]Hash, error) {
	roots := make([][]Hash, len(adds))
	for i, add := range adds {
		roots[i] = make([]Hash, len(s.Roots))
		copy(roots[i], s.Roots)

		_, err := s.Update(nil, []Hash{add}, Proof{})
		if err != nil {
			return nil, err
		}
	}

	return roots, nil
}

// undoAdd will remove the additions that had happened and will place empty roots back to where they were.
func (m *MapPollard) undoAdd(adds []Hash, origPrevRoots []Hash) error {
	s := Stump{
		Roots:     make([]Hash, len(origPrevRoots)),
		NumLeaves: m.NumLeaves - uint64(len(adds)),
	}
	copy(s.Roots, origPrevRoots)

	prevRoots, err := getSingleRoots(s, adds)
	if err != nil {
		return err
	}
	for i := len(prevRoots) - 1; i >= 0; i-- {
		prevRoot := prevRoots[i]
		err = m.undoSingleAdd(prevRoot)
		if err != nil {
			return err
		}
	}

	return err
}

// Undo will undo the last modify. The numAdds, proof, hashes, MUST be the data from the previous modify.
// The origPrevRoots MUST be the roots that this Undo will go back to.
func (m *MapPollard) UndoWithTTLs(adds []Hash, createIndex []int32,
	proof Proof, hashes, origPrevRoots []Hash) error {

	m.rwLock.Lock()
	defer m.rwLock.Unlock()

	s := Stump{
		Roots:     make([]Hash, len(origPrevRoots)),
		NumLeaves: m.NumLeaves - uint64(len(adds)),
	}
	copy(s.Roots, origPrevRoots)
	_, err := s.Update(hashes, nil, proof)
	if err != nil {
		return fmt.Errorf("Undo errored while undoing added leaves. %v", err)
	}

	// TODO: figure out undo adds with view as well.
	err = m.undoAdd(adds, s.Roots)
	if err != nil {
		return fmt.Errorf("Undo errored while undoing added leaves. %v", err)
	}

	ingestIns, undoInfo, _, err := generateIngestAndUndoInfo(m.NumLeaves, hashes, proof)
	if err != nil {
		return err
	}

	view, err := m.getViewForUndo(undoInfo)
	if err != nil {
		return err
	}

	err = view.undoDeletion(createIndex, undoInfo, ingestIns, hashes)
	if err != nil {
		return fmt.Errorf("Undo errored while undoing deleted leaves. %v", err)
	}

	m.commitView(view)
	return nil
}

// Undo will undo the last modify. The numAdds, proof, hashes, MUST be the data from the previous modify.
// The origPrevRoots MUST be the roots that this Undo will go back to.
func (m *MapPollard) Undo(adds []Hash, proof Proof, hashes, origPrevRoots []Hash) error {
	m.rwLock.Lock()
	defer m.rwLock.Unlock()

	s := Stump{
		Roots:     make([]Hash, len(origPrevRoots)),
		NumLeaves: m.NumLeaves - uint64(len(adds)),
	}
	copy(s.Roots, origPrevRoots)
	_, err := s.Update(hashes, nil, proof)
	if err != nil {
		return fmt.Errorf("Undo errored while undoing added leaves. %v", err)
	}

	// TODO: figure out undo adds with view as well.
	err = m.undoAdd(adds, s.Roots)
	if err != nil {
		return fmt.Errorf("Undo errored while undoing added leaves. %v", err)
	}

	ingestIns, undoInfo, _, err := generateIngestAndUndoInfo(m.NumLeaves, hashes, proof)
	if err != nil {
		return err
	}

	view, err := m.getViewForUndo(undoInfo)
	if err != nil {
		return err
	}

	err = view.undoDeletion(nil, undoInfo, ingestIns, hashes)
	if err != nil {
		return fmt.Errorf("Undo errored while undoing deleted leaves. %v", err)
	}

	m.commitView(view)
	return nil
}

// calculatePosition returns the position of the given hash and node.
func (m *MapPollard) calculatePosition(hash Hash, node Node) (uint64, error) {
	// Tells whether to follow the left child or the right child when going
	// down the tree. 0 means left, 1 means right.
	leftRightIndicator := uint64(0)

	rowsToTop := 0
	for node.Above != empty {
		aboveNode, found := m.Nodes.Get(node.Above)
		if !found {
			return 0, fmt.Errorf("calculatePosition err: node %v points to above node of %v "+
				"but it's not found", hash, node.Above)
		}

		if aboveNode.LBelow == hash {
			// Left
			leftRightIndicator <<= 1
		} else {
			// Right
			leftRightIndicator <<= 1
			leftRightIndicator |= 1
		}

		hash = node.Above
		node = aboveNode

		// Ugly but need to flip the bit that we set in this loop as the roots
		// don't point their children instead of their nieces.
		if rowsToTop == 0 {
			leftRightIndicator ^= 1
		}
		rowsToTop++
	}
	forestRows := TreeRows(m.NumLeaves)

	// Calculate which row the root is on.
	rootRow := -1
	// Start from the lowest root.
	rootIdx := len(m.Roots) - 1
	for h := 0; h <= int(forestRows); h++ {
		// Because every root represents a perfect tree of every leaf
		// we ever added, each root position will be a power of 2.
		//
		// Go through the bits of NumLeaves. Every bit that is on
		// represents a root.
		if (m.NumLeaves>>h)&1 == 1 {
			// If we found the root, save the row to rootRow
			// and return.
			if m.Roots[rootIdx] == hash {
				rootRow = h
				break
			}

			// Check the next higher root.
			rootIdx--
		}
	}

	// Start from the root and work our way down the position that we want.
	retPos := rootPosition(m.NumLeaves, uint8(rootRow), forestRows)

	for i := 0; i < rowsToTop; i++ {
		isRight := uint64(1) << i
		if leftRightIndicator&isRight == isRight {
			// Grab the sibling since the pollard nodes point to their
			// niece. My sibling's nieces are my children.
			retPos = sibling(RightChild(retPos, forestRows))
		} else {
			// Grab the sibling since the pollard nodes point to their
			// niece. My sibling's nieces are my children.
			retPos = sibling(LeftChild(retPos, forestRows))
		}
	}

	return retPos, nil
}

// cached checks if the given hashes are cached.
func (m *MapPollard) cached(hashes []Hash) bool {
	for _, hash := range hashes {
		_, found := m.Nodes.Get(hash)
		if !found {
			return found
		}
	}

	return true
}

// Prove returns a proof of all the targets that are passed in.
// TODO: right now it refuses to prove anything but the explicitly cached leaves.
// There may be some leaves that it could prove that's not cached due to the proofs
// overlapping.
func (m *MapPollard) Prove(proveHashes []Hash) (Proof, error) {
	m.rwLock.RLock()
	defer m.rwLock.RUnlock()

	// Check that the targets are proveable.
	if !m.cached(proveHashes) {
		return Proof{}, fmt.Errorf("Cannot prove:\n%s\nas not all of them are cached",
			printHashes(proveHashes))
	}

	hashMap := make(map[Hash]uint64, len(proveHashes)*2)
	canCalcMap := make(map[uint64]Hash, len(proveHashes)*2)

	var err error
	origTargets := make([]uint64, len(proveHashes))
	for i := range origTargets {
		n, _ := m.Nodes.Get(proveHashes[i])
		origTargets[i], err = m.calculatePosition(proveHashes[i], n)
		if err != nil {
			return Proof{}, err
		}

		// Nothing more to do if I'm a root.
		if n.isRoot() {
			continue
		}

		// Add myself.
		hashMap[proveHashes[i]] = origTargets[i]

		// Get sibhash.
		aNode, found := m.Nodes.Get(n.Above)
		if !found {
			return Proof{}, fmt.Errorf("%v's above of %v not found",
				proveHashes[i], n.Above)
		}
		sibHash, _, err := aNode.getSibHash(proveHashes[i])
		if err != nil {
			return Proof{}, err
		}

		// Add the sibhash to the hashMap.
		hashMap[sibHash] = sibling(origTargets[i])

		hash := n.Above
		n = aNode
		parentPos := Parent(origTargets[i], m.TotalRows)
		pos := sibling(parentPos)

		for !n.isRoot() {
			// Add sibling as calculatable.
			hashMap[hash] = pos

			aNode, found = m.Nodes.Get(n.Above)
			if !found {
				return Proof{}, fmt.Errorf("%v's above of %v not found",
					hash, n.Above)
			}

			canCalcMap[sibling(pos)], _, err = aNode.getSibHash(hash)
			if err != nil {
				return Proof{}, err
			}

			hash = n.Above
			pos = sibling(Parent(pos, m.TotalRows))
			n = aNode
		}
	}

	for _, hash := range proveHashes {
		delete(hashMap, hash)
	}

	for _, hash := range canCalcMap {
		delete(hashMap, hash)
	}

	hnp := hashAndPos{
		positions: make([]uint64, 0, len(hashMap)),
		hashes:    make([]Hash, 0, len(hashMap)),
	}
	for k, v := range hashMap {
		hnp.Append(v, k)
	}

	sort.Sort(hnp)
	return Proof{Targets: origTargets, Proof: hnp.hashes}, nil
}

// VerifyPartialProof takes partial proof of the targets and attempts to prove their existence.
// If the remember bool is false, the accumulator is not modified. If it is true, the necessary
// hashes to prove the targets are cached.
//
// NOTE: proofHashes MUST be sorted in relation to their positions in the accumulator.
func (m *MapPollard) VerifyPartialProof(origTargets []uint64, delHashes, proofHashes []Hash, remember bool) error {
	m.rwLock.Lock()
	defer m.rwLock.Unlock()

	// Sort targets first. Copy to avoid mutating the original.
	targets := copySortedFunc(origTargets, uint64Cmp)

	// Figure out what hashes at which positions are needed.
	proofPositions, _ := ProofPositions(targets, m.NumLeaves, TreeRows(m.NumLeaves))

	// Translate the proof positions if needed.
	if TreeRows(m.NumLeaves) != m.TotalRows {
		proofPositions = translatePositions(proofPositions, TreeRows(m.NumLeaves), m.TotalRows)
	}

	// Where we'll merge the hashes that we already have with the proofHashes provided.
	allProofHashes := make([]Hash, 0, len(proofPositions))

	proofHashIdx := 0
	for _, pos := range proofPositions {
		leaf, _ := m.Nodes.Get(pos)
		hash := leaf.Hash
		if hash == empty {
			// We couldn't fetch the hash from the accumulator so it should
			// be provided in the proofHashes.
			if len(proofHashes) <= proofHashIdx {
				return fmt.Errorf("proof too short")
			}
			allProofHashes = append(allProofHashes, proofHashes[proofHashIdx])
			proofHashIdx++
		} else {
			// We have the hash so use that instead.
			allProofHashes = append(allProofHashes, hash)
		}
	}

	// Verify the proof we put together.
	return m.verify(delHashes, Proof{origTargets, allProofHashes}, remember)
}

// GetMissingPositions returns all the missing positions that are needed to verify the given
// targets.
//
// This function is safe for concurrent access.
func (m *MapPollard) GetMissingPositions(origTargets []uint64) []uint64 {
	if len(origTargets) == 0 {
		return []uint64{}
	}

	m.rwLock.RLock()
	defer m.rwLock.RUnlock()

	// Sort targets first. Copy to avoid mutating the original.
	targets := copySortedFunc(origTargets, uint64Cmp)

	// Generate the positions needed to prove this.
	proofPos, _ := ProofPositions(targets, m.NumLeaves, TreeRows(m.NumLeaves))
	if TreeRows(m.NumLeaves) != m.TotalRows {
		proofPos = translatePositions(proofPos, TreeRows(m.NumLeaves), m.TotalRows)
	}

	// Go through all the proof positions and mark the ones that are missing.
	missingPositions := make([]uint64, 0, len(proofPos))
	for i := range proofPos {
		pos := proofPos[i]
		h, _, _, _, _ := m.getNodeByPos(pos)
		if h == empty {
			missingPositions = append(missingPositions, pos)
		}
	}

	return missingPositions
}

// getNodeByPos returns the node, it's sibling, and the parent of the given position.
//
// This function is NOT safe for concurrent access.
func (m *MapPollard) getNodeByPos(pos uint64) (nHash Hash, n, sibling, parent *Node, err error) {
	// Tree is the root the position is located under.
	// branchLen denotes how far down the root the position is.
	// bits tell us if we should go down to the left child or the right child.
	if pos >= maxPosition(TreeRows(m.NumLeaves)) {
		return Hash{}, nil, nil, nil,
			fmt.Errorf("Position %d does not exist in tree of %d leaves", pos, m.NumLeaves)
	}
	tree, branchLen, bits, err := DetectOffset(pos, m.NumLeaves)
	if err != nil {
		return Hash{}, nil, nil, nil, err
	}
	if tree >= uint8(len(m.Roots)) {
		return Hash{}, nil, nil, nil, fmt.Errorf("getNode error: couldn't fetch %d, "+
			"calculated root index of %d but only have %d roots",
			pos, tree, len(m.Roots))
	}

	if m.Roots[tree] == empty {
		return empty, nil, nil, nil, nil
	}

	// Initialize.
	n, sibling, parent = m.getNodeByHash(m.Roots[tree]), m.getNodeByHash(m.Roots[tree]), nil
	nHash = m.Roots[tree]

	if n == nil {
		return Hash{}, nil, nil, nil, nil
	}

	// Go down the tree to find the node we're looking for.
	for h := int(branchLen) - 1; h >= 0; h-- {
		// Parent is the sibling of the current node as each of the
		// nodes point to their nieces.
		parent = sibling

		// Figure out which node we need to follow.
		niecePos := uint8(bits>>h) & 1
		if isLeftNiece(uint64(niecePos)) {
			nHash = n.LBelow
			n, sibling = m.getNodeByHash(n.LBelow), m.getNodeByHash(n.RBelow)
		} else {
			nHash = n.RBelow
			n, sibling = m.getNodeByHash(n.RBelow), m.getNodeByHash(n.LBelow)
		}

		// Return early if the path to the node we're looking for
		// doesn't exist.
		if n == nil {
			return Hash{}, nil, nil, nil, nil
		}
	}

	return
}

// getNodeByHash returns the node from Nodes. Nil if not found.
//
// This function is NOT safe for concurrent access.
func (m *MapPollard) getNodeByHash(hash Hash) *Node {
	node, found := m.Nodes.Get(hash)
	if !found {
		return nil
	}

	return &node
}

// Verify returns an error if the given proof and the delHashes do not hash up to the stored roots.
// Passing the remember flag as true will cause the proof to be cached.
//
// This function is safe for concurrent access.
func (m *MapPollard) Verify(delHashes []Hash, proof Proof, remember bool) error {
	m.rwLock.Lock()
	defer m.rwLock.Unlock()

	return m.verify(delHashes, proof, remember)
}

// verify returns an error if the given proof and the delHashes do not hash up to the stored roots.
// Passing the remember flag as true will cause the proof to be cached.
//
// This function is different from Verify() in that it's not safe for concurrent access.
func (m *MapPollard) verify(delHashes []Hash, proof Proof, remember bool) error {
	ingestIns, _, rootCandidates, err := generateIngestAndUndoInfo(m.NumLeaves, delHashes, proof)
	if err != nil {
		return err
	}

	rootIndexes := make([]int, 0, len(rootCandidates))
	for i := range m.Roots {
		if len(rootCandidates) > len(rootIndexes) &&
			m.Roots[len(m.Roots)-(i+1)] == rootCandidates[len(rootIndexes)] {

			rootIndexes = append(rootIndexes, len(m.Roots)-(i+1))
		}
	}

	if len(rootCandidates) != len(rootIndexes) {
		// The proof is invalid because some root candidates were not
		// included in `roots`.
		err := fmt.Errorf("MapPollard Verify fail. Invalid proof. Have %d roots but only "+
			"matched %d roots", len(rootCandidates), len(rootIndexes))
		return err
	}

	if remember {
		return m.ingest(ingestIns)
	}

	return nil
}

// Ingest places the proof in the tree and remembers them.
//
// NOTE: there's no verification done that the passed in proof is valid. It's the
// caller's responsibility to verify that the given proof is valid.
func (m *MapPollard) Ingest(delHashes []Hash, proof Proof) error {
	m.rwLock.Lock()
	defer m.rwLock.Unlock()

	ingestIns, _, _, err := generateIngestAndUndoInfo(m.NumLeaves, delHashes, proof)
	if err != nil {
		return err
	}

	return m.ingest(ingestIns)
}

// ingest places the proof in the tree and remembers them.
//
// NOTE: there's no verification done that the passed in proof is valid. It's the
// caller's responsibility to verify that the given proof is valid.
//
// This function is different from Ingest() in that it's not safe for concurrent access.
func (m *MapPollard) ingest(ins ingestInstruction) error {
	if len(ins.Hashes)%3 != 0 {
		return fmt.Errorf("ingest hash length of %v is malformed as "+
			"it's not divisible by 3", len(ins.Hashes))
	}

	for i := len(ins.Hashes) - 1; i >= 0; i-- {
		hash := ins.Hashes[i]
		rBelow := ins.Hashes[i-1]
		lBelow := ins.Hashes[i-2]
		rRem := ins.isLeaf[i-1]
		lRem := ins.isLeaf[i-2]

		node, found := m.Nodes.Get(hash)
		if !found {
			return fmt.Errorf("node hash %v not found", hash)
		}
		if node.RBelow != empty {
			i--
			i--
			continue
		}

		node.LBelow = lBelow
		node.RBelow = rBelow
		m.Nodes.Put(hash, node)

		rNode := Node{
			Remember: rRem || m.Full,
			Above:    hash,
			AddIndex: -1,
		}
		m.Nodes.Put(rBelow, rNode)

		lNode := Node{
			Remember: lRem || m.Full,
			Above:    hash,
			AddIndex: -1,
		}
		m.Nodes.Put(lBelow, lNode)

		i--
		i--
	}

	return nil
}

// fetchNodeForDel fetches all the nodes that are needed to remove the given hash.
func (m *MapPollard) fetchNodeForDel(hash Hash) (
	node, sibNode, aNode Node, sibHash Hash, foundNode bool, err error) {

	node, foundNode = m.Nodes.Get(hash)
	if !foundNode {
		return
	}

	if node.isRoot() {
		return
	}

	var found bool
	aNode, found = m.Nodes.Get(node.Above)
	if !found {
		err = fmt.Errorf("node %v points to above of %v but wasn't found",
			hash, node.Above)
		return
	}

	sibHash, _, err = aNode.getSibHash(hash)
	if err != nil {
		return
	}

	sibNode, found = m.Nodes.Get(sibHash)
	if !found {
		err = fmt.Errorf("node %v has l %v, r %v but %v wasn't found",
			node.Above, node.LBelow, node.RBelow, sibHash)
		return
	}

	return
}

// maybeForget checks to see if the hash can be pruned from the accumulator. If it can, it prunes
// it and recursively calls itself again to see if the above node can be forgotten as well.
func (m *MapPollard) maybeForget(hash Hash) error {
	n, found := m.Nodes.Get(hash)
	if !found {
		return nil
	}

	var canPrune bool
	if n.LBelow == empty && n.RBelow == empty {
		canPrune = true
	} else {
		l, found := m.Nodes.Get(n.LBelow)
		if !found {
			return fmt.Errorf("%v points to %v but not found", hash, n.LBelow)
		}
		r, found := m.Nodes.Get(n.RBelow)
		if !found {
			return fmt.Errorf("%v points to %v but not found", hash, n.RBelow)
		}

		var err error
		canPrune, err = l.pruneable(r)
		if err != nil {
			return err
		}
	}

	if canPrune {
		m.Nodes.Delete(n.LBelow)
		m.Nodes.Delete(n.RBelow)

		n.LBelow = empty
		n.RBelow = empty
		m.Nodes.Put(hash, n)

		if n.Above != empty {
			err := m.maybeForget(n.Above)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

// Prune prunes the passed in hashes and the proofs for them. Will not prune the proof if it's
// needed for another cached hash.
func (m *MapPollard) Prune(hashes []Hash) error {
	if m.Full {
		return nil
	}

	m.rwLock.Lock()
	defer m.rwLock.Unlock()

	for _, hash := range hashes {
		node, sibNode, aNode, sibHash, found, err := m.fetchNodeForDel(hash)
		if err != nil {
			return err
		}
		if !found {
			continue
		}

		if node.isRoot() {
			continue
		}

		node.Remember = false
		canPrune, err := node.pruneable(sibNode)
		if err != nil {
			return err
		}

		if !canPrune {
			continue
		}

		m.Nodes.Delete(sibHash)
		m.Nodes.Delete(hash)

		aNode.RBelow = empty
		aNode.LBelow = empty
		m.Nodes.Put(node.Above, aNode)

		err = m.maybeForget(node.Above)
		if err != nil {
			return err
		}
	}

	return nil
}

// getRoots returns the hashes of the roots.
func (m *MapPollard) GetRoots() []Hash {
	m.rwLock.RLock()
	defer m.rwLock.RUnlock()

	roots, _ := m.getRoots()
	return roots
}

// getRoots returns the root hashes and their positions.
//
// This function is different from GetRoots() in that it's not safe for concurrent access.
func (m *MapPollard) getRoots() ([]Hash, []uint64) {
	nRoots := numRoots(m.NumLeaves)

	roots := make([]Hash, 0, nRoots)
	rootPositions := RootPositions(m.NumLeaves, m.TotalRows)
	for _, rootPosition := range rootPositions {
		node, _ := m.Nodes.Get(rootPosition)
		roots = append(roots, node.Hash)
	}

	return roots, rootPositions
}

// GetHash returns the hash for the given position. Empty hash (all values are 0) is returned
// if the given position is not cached.
func (m *MapPollard) GetHash(pos uint64) Hash {
	m.rwLock.RLock()
	defer m.rwLock.RUnlock()

	if m.TotalRows != TreeRows(m.NumLeaves) {
		pos = translatePos(pos, TreeRows(m.NumLeaves), m.TotalRows)
	}
	leaf, _ := m.Nodes.Get(pos)
	return leaf.Hash
}

// getLeafPosition returns the position of the leaf for the given hash and returns false
// if the leaf hash doesn't exist.
//
// MUST be called with the lock held.
func (m *MapPollard) getLeafHashPosition(hash Hash) (uint64, bool) {
	cachedLeaf, found := m.CachedLeaves.Get(hash)
	if !found {
		return 0, false
	}
	pos := cachedLeaf.Position

	if m.TotalRows != TreeRows(m.NumLeaves) {
		pos = translatePos(pos, m.TotalRows, TreeRows(m.NumLeaves))
	}

	return pos, true
}

// GetLeafPosition returns the position of the leaf for the given hash. Returns false if
// the hash is not the hash of a leaf or if the hash wasn't found in the accumulator.
func (m *MapPollard) GetLeafPosition(hash Hash) (uint64, bool) {
	m.rwLock.RLock()
	defer m.rwLock.RUnlock()

	return m.getLeafHashPosition(hash)
}

// GetNumLeaves returns the number of leaves that were ever added to the accumulator.
func (m *MapPollard) GetNumLeaves() uint64 {
	return m.NumLeaves
}

// GetTreeRows returns the tree rows that are allocated for this accumulator.
func (m *MapPollard) GetTreeRows() uint8 {
	return m.TotalRows
}

// GetStump returns a stump with the values fetched from the pollard.
func (m *MapPollard) GetStump() Stump {
	m.rwLock.RLock()
	defer m.rwLock.RUnlock()

	return m.getStump()
}

// getStump returns a stump with the values fetched from the pollard.
//
// This function is different from GetStump() in that it's not safe for concurrent access.
func (m *MapPollard) getStump() Stump {
	roots, _ := m.getRoots()
	return Stump{Roots: roots, NumLeaves: m.NumLeaves}
}

// GetLeafHashPositions returns the positions for the given leaf hashes.
// If the leaf hash doesn't exist or if the leaf hash isn't cached, it'll be the
// default value of 0.
func (m *MapPollard) GetLeafHashPositions(hashes []Hash) []uint64 {
	m.rwLock.RLock()
	defer m.rwLock.RUnlock()

	positions := make([]uint64, len(hashes))
	for i := range positions {
		pos, found := m.getLeafHashPosition(hashes[i])
		if found {
			positions[i] = pos
		}
	}

	return positions
}

// NewMapPollardFromRoots returns a new MapPollard initialized with the roots and the
// numLeaves that was passed in.
func NewMapPollardFromRoots(rootHashes []Hash, numLeaves uint64) MapPollard {
	m := NewMapPollard(false)
	m.NumLeaves = numLeaves

	rootPositions := RootPositions(m.NumLeaves, m.TotalRows)
	for i, rootPosition := range rootPositions {
		m.Nodes.Put(rootPosition, Leaf{Hash: rootHashes[i]})
	}

	return m
}

// writeOne writes the given node to the writer. It's recursive and calls itself if
// the passed in Node has below nodes.
func (m *MapPollard) writeOne(hash Hash, n Node, w io.Writer) (int, error) {
	totalBytes := 0

	// Write hash.
	wroteBytes, err := w.Write(hash[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += wroteBytes

	if hash == empty {
		return totalBytes, nil
	}

	// Write remember.
	if n.Remember {
		wroteBytes, err = w.Write([]byte{1})
		if err != nil {
			return totalBytes, err
		}
	} else {
		wroteBytes, err = w.Write([]byte{0})
		if err != nil {
			return totalBytes, err
		}
	}
	totalBytes += wroteBytes

	// Write add index.
	var buf [4]byte
	binary.LittleEndian.PutUint32(buf[:], uint32(n.AddIndex))
	wroteBytes, err = w.Write(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += wroteBytes

	// If below nodes are present, then call writeOne on those nieces as well and
	// mark as nieces being present. If they don't exist, just mark as nieces
	// missing and move on.
	if n.LBelow != empty && n.RBelow != empty {
		wroteBytes, err := w.Write([]byte{1})
		if err != nil {
			return totalBytes, err
		}
		totalBytes += wroteBytes

		lNode, found := m.Nodes.Get(n.LBelow)
		if !found {
			return totalBytes, fmt.Errorf("lBelow of %v not found", n.LBelow)
		}

		leftBytes, err := m.writeOne(n.LBelow, lNode, w)
		if err != nil {
			return totalBytes, err
		}
		totalBytes += leftBytes

		rNode, found := m.Nodes.Get(n.RBelow)
		if !found {
			return totalBytes, fmt.Errorf("lBelow of %v not found", n.LBelow)
		}
		rightBytes, err := m.writeOne(n.RBelow, rNode, w)
		if err != nil {
			return totalBytes, err
		}
		totalBytes += rightBytes
	} else {
		wroteBytes, err := w.Write([]byte{0})
		if err != nil {
			return totalBytes, err
		}
		totalBytes += wroteBytes
	}

	return totalBytes, nil

}

// readOne reads a node from the reader. It's recursive and calls itself if the node
// it just read has below nodes.
func (m *MapPollard) readOne(above Hash, r io.Reader) (int64, Hash, error) {
	totalBytes := int64(0)

	var hash Hash
	node := Node{Above: above}

	// Read from the reader. If we're at EOF, we've finished restoring
	// the pollard.
	readBytes, err := r.Read(hash[:])
	if err != nil {
		if err == io.EOF {
			return int64(readBytes), Hash{}, nil
		}
		return totalBytes, Hash{}, err
	}
	totalBytes += int64(readBytes)

	if hash == empty {
		return totalBytes, hash, nil
	}

	// Read remember.
	var buf [8]byte
	readBytes, err = r.Read(buf[:1])
	if err != nil {
		return totalBytes, Hash{}, err
	}
	totalBytes += int64(readBytes)

	if buf[0] == 1 {
		node.Remember = true
	}

	readBytes, err = r.Read(buf[:4])
	if err != nil {
		return totalBytes, Hash{}, err
	}
	totalBytes += int64(readBytes)

	node.AddIndex = int32(binary.LittleEndian.Uint32(buf[:]))

	// Read if the node has nieces. If the node does have nieces, then we call readOne
	// for the nieces as well.
	readBytes, err = r.Read(buf[:1])
	if err != nil {
		return totalBytes, hash, err
	}
	totalBytes += int64(readBytes)

	// Return early.
	if buf[0] == 0 {
		m.Nodes.Put(hash, node)
		return totalBytes, hash, err
	}

	if buf[0] == 1 {
		leftBytes, lHash, err := m.readOne(hash, r)
		if err != nil {
			return totalBytes, hash, err
		}
		totalBytes += leftBytes
		node.LBelow = lHash

		rightBytes, rHash, err := m.readOne(hash, r)
		if err != nil {
			return totalBytes, hash, err
		}
		totalBytes += rightBytes
		node.RBelow = rHash
	}
	m.Nodes.Put(hash, node)

	return totalBytes, hash, nil
}

// Write writes the entire pollard to the writer.
func (m *MapPollard) Write(w io.Writer) (int, error) {
	m.rwLock.RLock()
	defer m.rwLock.RUnlock()

	totalBytes := 0

	var buf [8]byte

	// Write the total rows.
	buf[0] = m.TotalRows
	bytes, err := w.Write(buf[:1])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += bytes

	// Write the number of leaves.
	binary.LittleEndian.PutUint64(buf[:], m.NumLeaves)
	bytes, err = w.Write(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += bytes

	// Write the count for the node elements in the map.
	binary.LittleEndian.PutUint64(buf[:], uint64(m.Nodes.Length()))
	bytes, err = w.Write(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += bytes

	// Write the count for the roots.
	bytes, err = w.Write([]byte{uint8(len(m.Roots))})
	if err != nil {
		return totalBytes, err
	}
	totalBytes += bytes

	// Then write the entire map pollard to the writer.
	for _, root := range m.Roots {
		var node Node
		if root != empty {
			var found bool
			node, found = m.Nodes.Get(root)
			if !found {
				return totalBytes, fmt.Errorf("root %v not found in nodes", root)
			}
		}

		bytes, err := m.writeOne(root, node, w)
		if err != nil {
			return totalBytes, err
		}
		totalBytes += bytes
	}

	return totalBytes, nil
}

// Read reads the pollard from the reader into the map pollard variable.
func (m *MapPollard) Read(r io.Reader) (int, error) {
	m.rwLock.Lock()
	defer m.rwLock.Unlock()

	totalBytes := 0

	var buf [8]byte

	// Read the total rows.
	bytes, err := r.Read(buf[:1])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += bytes

	m.TotalRows = buf[0]

	// Read the number of leaves.
	bytes, err = r.Read(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += bytes
	m.NumLeaves = binary.LittleEndian.Uint64(buf[:])

	// Read num nodes.
	bytes, err = r.Read(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += bytes

	numNodes := binary.LittleEndian.Uint64(buf[:])
	m.Nodes = newNodesMap(int(numNodes))

	// Read the count for the roots.
	bytes, err = r.Read(buf[:1])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += bytes

	numRoots := buf[0]
	m.Roots = make([]Hash, numRoots)

	// Read elements and put them in the map.
	for i := range m.Roots {
		bytes, rootHash, err := m.readOne(empty, r)
		if err != nil {
			return totalBytes, err
		}

		m.Roots[i] = rootHash
		totalBytes += int(bytes)
	}

	return totalBytes, nil
}
