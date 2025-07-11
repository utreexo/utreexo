package utreexo

import (
	"encoding/binary"
	"fmt"
	"io"
	"sync"

	"golang.org/x/exp/slices"
)

var emptyNode Node

type Node struct {
	// Remember indicates if this node should be remembered.
	Remember bool

	// The left and right child of this node.
	lBelow, rBelow, above Hash

	// AddIndex indicates which leaf it was at the height the leaf was added.
	// -1 if it's not a leaf.
	AddIndex int32
}

func (n *Node) deadEnd() bool {
	return n.lBelow == empty && n.rBelow == empty
}

func (n *Node) pruneable(sib Node) (bool, error) {
	if sib.above != n.above {
		return false, fmt.Errorf("given sib points to %v while I point to %v",
			sib.above, n.above)
	}

	if sib.Remember || n.Remember {
		return false, nil
	}

	return n.deadEnd() && sib.deadEnd(), nil
}

func (n *Node) getSibHash(hash Hash) (Hash, bool, error) {
	// Grab sibling.
	if hash == n.lBelow {
		return n.rBelow, false, nil
	} else if hash == n.rBelow {
		return n.lBelow, true, nil
	} else {
		return empty, false, fmt.Errorf("above node for hash %v points to left %v and right %v",
			hash, n.lBelow, n.rBelow)
	}
}

func (n *Node) isRoot() bool {
	return n.above == empty
}

func (n *Node) String() string {
	return fmt.Sprintf("rememeber %v, above %v, l %v, r %v, addIndex %v",
		n.Remember, n.above, n.lBelow, n.rBelow, n.AddIndex)
}

// Assert that MapPollard implements the Utreexo interface.
var _ Utreexo = (*MapPollard)(nil)

// NodesInterface models the interface for the data storage for the map pollard.
type NodesInterface interface {
	Get(Hash) (Node, bool)

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

	Roots []Hash

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
		rwLock:    new(sync.RWMutex),
		Nodes:     newNodesMap(0),
		TotalRows: 0,
		Full:      full,
	}
}

// Modify takes in the additions and deletions and updates the accumulator accordingly.
func (m *MapPollard) Modify(adds []Leaf, delHashes []Hash, proof Proof) error {
	m.rwLock.Lock()
	defer m.rwLock.Unlock()

	_, ins, _, _, err := calculateHashes2(m.NumLeaves, delHashes, proof)
	if err != nil {
		return err
	}

	err = m.remove(ins)
	if err != nil {
		return err
	}

	err = m.add(adds)
	if err != nil {
		return err
	}

	return nil
}

// Modify takes in the additions and deletions and updates the accumulator accordingly.
// It returns the created heights and the indexes of the deleted leaves. The height and the index
// returns as math.MaxUint32 if the leaves were added with ingest or if they were a result of
// and Undo with the ttls being provided.
func (m *MapPollard) ModifyAndReturnTTLs(adds []Leaf, delHashes []Hash, proof Proof) (
	[]uint32, error) {

	m.rwLock.Lock()
	defer m.rwLock.Unlock()

	createIndexes := make([]uint32, 0, len(delHashes))
	for _, delHash := range delHashes {
		leafInfo, _ := m.Nodes.Get(delHash)
		createIndexes = append(createIndexes, uint32(leafInfo.AddIndex))
	}

	_, ins, _, _, err := calculateHashes2(m.NumLeaves, delHashes, proof)
	if err != nil {
		return nil, err
	}

	err = m.remove(ins)
	if err != nil {
		return nil, err
	}

	err = m.add(adds)
	if err != nil {
		return nil, err
	}

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

// add adds the slice of leaves to the accumulator.  It caches the leaves that have the
// remember field set to true.
func (m *MapPollard) add(adds []Leaf) error {
	for i, add := range adds {
		// Add to the accumulator.
		err := m.addSingle(add, i)
		if err != nil {
			return err
		}

		m.NumLeaves++
	}

	return nil
}

// updateAbove makes n's belows point to newHash.
func (m *MapPollard) updateAbove(n Node, newHash Hash) error {
	if n.lBelow == empty {
		return nil
	}

	lBelow, lfound := m.Nodes.Get(n.lBelow)
	rBelow, rfound := m.Nodes.Get(n.rBelow)
	if !lfound && !rfound {
		return nil
	}

	if !lfound || !rfound {
		return fmt.Errorf("n points to lBelow of %v and rBelow of %v "+
			"but only one of them exists", n.lBelow, n.rBelow)
	}

	lBelow.above = newHash
	rBelow.above = newHash

	m.Nodes.Put(n.lBelow, lBelow)
	m.Nodes.Put(n.rBelow, rBelow)

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
	a.lBelow, a.rBelow, b.lBelow, b.rBelow =
		b.lBelow, b.rBelow, a.lBelow, a.rBelow

	return a, b, err
}

// a gives its below nodes to b.
func (m *MapPollard) giveBelow(a, b Node, bHash Hash) (Node, Node, error) {
	err := m.updateAbove(a, bHash)
	if err != nil {
		return a, b, err
	}

	b.lBelow, b.rBelow = a.lBelow, a.rBelow
	a.lBelow, a.rBelow = empty, empty
	return a, b, nil
}

// addSingle adds one leaf to the accumulator.  If the remember field is set to true, the leaf
// will be cached.
func (m *MapPollard) addSingle(add Leaf, index int) error {
	if TreeRows(m.NumLeaves+1) > m.TotalRows {
		m.TotalRows++
	}

	// If the map pollard is configured to be full, override the remember value in the leaf.
	if m.Full {
		add.Remember = true
	}

	addHash := add.Hash
	addNode := Node{Remember: add.Remember, AddIndex: int32(index)}
	m.Nodes.Put(add.Hash, addNode)

	for h := uint8(0); (m.NumLeaves>>h)&1 == 1; h++ {
		// Grab and pop off the root that will become a node.
		var root Hash
		root, m.Roots = m.Roots[len(m.Roots)-1], m.Roots[:len(m.Roots)-1]

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
		curRootNode, found := m.Nodes.Get(root)
		if !found {
			return fmt.Errorf("root node %v not found", root)
		}

		// Make parent node.
		pNode := Node{lBelow: root, rBelow: addHash, AddIndex: -1, Remember: m.Full}
		parentHash := parentHash(root, addHash)

		var err error
		curRootNode, addNode, err = m.swapBelow(curRootNode, addNode, root, addHash)
		if err != nil {
			return err
		}

		// Point to aunt or parent.
		addNode.above = parentHash
		curRootNode.above = parentHash

		// Update the nodes.
		m.Nodes.Put(addHash, addNode)
		m.Nodes.Put(root, curRootNode)

		// Prune if we can. The error only happens when both of the nodes do not point
		// to the same parent.
		canPrune, _ := addNode.pruneable(curRootNode)
		if canPrune {
			m.Nodes.Delete(addHash)
			m.Nodes.Delete(root)

			pNode.lBelow = empty
			pNode.rBelow = empty
		}
		m.Nodes.Put(parentHash, pNode)

		// Set the parent as the root being added for the next potential loop.
		addHash = parentHash
		addNode = pNode
	}

	m.Roots = append(m.Roots, addHash)

	return nil
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

// remove node removes the node of the given hash and all of its descendants from the map.
// If the node is a root, it'll mark the hash as a zombie root in the root hashes.
//
// NOTE: the parent of this node will still point to it afterwards. It's the caller's responsibility
// to deal with that.
func (m *MapPollard) removeNode(hash Hash, node Node) error {
	m.Nodes.Delete(hash)

	if node.isRoot() {
		// write the zombie root in the roots slice.
		idx := slices.Index(m.Roots, hash)
		if idx == -1 {
			return fmt.Errorf("couldn't find root of %v in the roots slice", hash)
		}
		m.Roots[idx] = empty
	}

	if node.lBelow != empty {
		lNode, found := m.Nodes.Get(node.lBelow)
		if !found {
			return nil
		}

		m.removeNode(node.lBelow, lNode)
	}

	if node.rBelow != empty {
		rNode, found := m.Nodes.Get(node.rBelow)
		if !found {
			return nil
		}

		m.removeNode(node.rBelow, rNode)
	}

	return nil
}

func (m *MapPollard) setAsSib(node, newSib Node, nodeHash, newSibHash Hash) (Node, Node, error) {
	// Get above node.
	aNode, found := m.Nodes.Get(node.above)
	if !found {
		return node, newSib, fmt.Errorf("node %v points to above of %v but wasn't found",
			nodeHash, node.above)
	}

	// Get the current sib of node.
	curSibHash, isLeft, err := aNode.getSibHash(nodeHash)
	if err != nil {
		return node, newSib, err
	}
	curSib, found := m.Nodes.Get(curSibHash)
	if !found {
		return node, newSib, fmt.Errorf("node %v has l %v, r %v but %v wasn't found",
			node.above, aNode.lBelow, aNode.rBelow, curSibHash)
	}

	// Node needs to point to the newSib's nieces.
	newSib, node, err = m.giveBelow(newSib, node, nodeHash)
	if err != nil {
		return node, newSib, err
	}

	// Get belows from the current sib.
	curSib, newSib, err = m.giveBelow(curSib, newSib, newSibHash)
	if err != nil {
		return node, newSib, err
	}

	// Set aNode to point to the new sib.
	if isLeft {
		aNode.lBelow = newSibHash
	} else {
		aNode.rBelow = newSibHash
	}

	// The new sib also need to point to the above node.
	newSib.above = node.above

	// Update all the nodes.
	m.Nodes.Delete(curSibHash)
	m.Nodes.Put(nodeHash, node)
	m.Nodes.Put(newSibHash, newSib)
	m.Nodes.Put(node.above, aNode)

	return node, newSib, nil
}

func (m *MapPollard) deleteNode(hash Hash) error {
	node, sibNode, aNode, sibHash, found, err := m.fetchNodeForDel(hash)
	if err != nil {
		return err
	}

	if !found {
		// It may not be cached. Nothing to do then.
		return nil
	}

	if node.isRoot() {
		return m.removeNode(hash, node)
	}

	// Swap below nodes.
	node, sibNode, err = m.swapBelow(node, sibNode, hash, sibHash)
	if err != nil {
		return err
	}
	m.removeNode(hash, node)

	// Sib becomes the root.
	if aNode.isRoot() {
		m.Nodes.Delete(node.above)
		idx := slices.Index(m.Roots, node.above)
		if idx == -1 {
			return fmt.Errorf("couldn't find root of %v in the roots slice", hash)
		}

		// Set sibling as the root.
		m.Roots[idx] = sibHash
		sibNode.above = empty
		m.Nodes.Put(sibHash, sibNode)

		return nil
	}

	// Move up the sibling.
	aNode, sibNode, err = m.setAsSib(aNode, sibNode, node.above, sibHash)
	if err != nil {
		return err
	}

	if m.Full {
		return nil
	}

	// Check if the sibling is prunable.
	canPrune, err := sibNode.pruneable(aNode)
	if err != nil {
		return err
	}

	if canPrune {
		gpNode, found := m.Nodes.Get(aNode.above)
		if !found {
			return fmt.Errorf("above node of %v not found for %v", aNode.above, node.above)
		}

		m.Nodes.Delete(node.above)
		m.Nodes.Delete(sibHash)

		gpNode.lBelow = empty
		gpNode.rBelow = empty
		m.Nodes.Put(aNode.above, gpNode)

		if gpNode.above != empty {
			err = m.maybeForget(gpNode.above)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

func (m *MapPollard) maybeForget(hash Hash) error {
	n, found := m.Nodes.Get(hash)
	if !found {
		return nil
	}

	var canPrune bool
	if n.lBelow == empty && n.rBelow == empty {
		canPrune = true
	} else {
		l, found := m.Nodes.Get(n.lBelow)
		if !found {
			return fmt.Errorf("%v points to %v but not found", hash, n.lBelow)
		}
		r, found := m.Nodes.Get(n.rBelow)
		if !found {
			return fmt.Errorf("%v points to %v but not found", hash, n.rBelow)
		}

		var err error
		canPrune, err = l.pruneable(r)
		if err != nil {
			return err
		}
	}

	if canPrune {
		m.Nodes.Delete(n.lBelow)
		m.Nodes.Delete(n.rBelow)

		n.lBelow = empty
		n.rBelow = empty
		m.Nodes.Put(hash, n)

		if n.above != empty {
			err := m.maybeForget(n.above)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

// updateHash updates the below and above nodes to point to the new hash and re-inserts
// the node with the new hash.
func (m *MapPollard) updateHash(before, after Hash) error {
	node, found := m.Nodes.Get(before)
	if !found {
		return nil
	}

	// Check if it's a root.
	if node.above == empty {
		idx := slices.Index(m.Roots, before)
		if idx == -1 {
			return fmt.Errorf("node %v doesn't have above but is "+
				"not in roots: %v", node, m.Roots)
		}
		m.Roots[idx] = after
	}

	m.Nodes.Delete(before)
	m.Nodes.Put(after, node)

	if node.above != empty {
		above, found := m.Nodes.Get(node.above)
		if !found {
			return fmt.Errorf("node %v points to %v but is "+
				"not found", before, node.above)
		}

		if above.lBelow == before {
			above.lBelow = after
		} else if above.rBelow == before {
			above.rBelow = after
		} else {
			return fmt.Errorf("updateHash above node for hash %v points to left %v and right %v",
				before, above.lBelow, above.rBelow)
		}

		m.Nodes.Put(node.above, above)
	}

	if node.lBelow != empty {
		lBelow, found := m.Nodes.Get(node.lBelow)
		if !found {
			return fmt.Errorf("node %v points to %v but is "+
				"not found", before, node.lBelow)
		}
		lBelow.above = after

		m.Nodes.Put(node.lBelow, lBelow)
	}

	if node.rBelow != empty {
		rBelow, found := m.Nodes.Get(node.rBelow)
		if !found {
			return fmt.Errorf("node %v points to %v but is "+
				"not found", before, node.rBelow)
		}
		rBelow.above = after

		m.Nodes.Put(node.rBelow, rBelow)
	}

	return nil
}

func (m *MapPollard) remove(ins ModifyInstruction) error {
	for i, afterHash := range ins.After {
		beforeHash := ins.Before[i]

		if afterHash == empty {
			err := m.deleteNode(beforeHash)
			if err != nil {
				return err
			}
		} else {
			err := m.updateHash(beforeHash, afterHash)
			if err != nil {
				return err
			}
		}
	}

	return nil
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
		if node.rBelow == empty && node.lBelow == empty {
			m.Roots = append(m.Roots, prevRoots[i])
			m.Nodes.Put(prevRoots[i], Node{AddIndex: -1})

			node = emptyNode
			rootHash = empty
			continue
		}

		rNode, found := m.Nodes.Get(node.rBelow)
		if !found {
			return fmt.Errorf("rBelow of %v for %v not found in nodes",
				node.rBelow, rootHash)
		}
		lNode, found := m.Nodes.Get(node.lBelow)
		if !found {
			return fmt.Errorf("lBelow of %v for %v not found in nodes",
				node.lBelow, rootHash)
		}

		// Swap and point to children.
		var err error
		rNode, lNode, err = m.swapBelow(rNode, lNode, node.rBelow, node.lBelow)
		if err != nil {
			return err
		}

		// Make lnode the root.
		lNode.above = empty
		m.Nodes.Put(node.lBelow, lNode)
		m.Roots = append(m.Roots, node.lBelow)

		// Remove rnode.
		m.Nodes.Delete(node.rBelow)

		// Set rNode as next node to be removed.
		rootHash = node.rBelow
		node = rNode
	}

	m.NumLeaves--
	m.TotalRows = TreeRows(m.NumLeaves)

	return nil
}

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
	aNode, found = m.Nodes.Get(node.above)
	if !found {
		err = fmt.Errorf("node %v points to above of %v but wasn't found",
			hash, node.above)
		return
	}

	sibHash, _, err = aNode.getSibHash(hash)
	if err != nil {
		return
	}

	sibNode, found = m.Nodes.Get(sibHash)
	if !found {
		err = fmt.Errorf("node %v has l %v, r %v but %v wasn't found",
			node.above, node.lBelow, node.rBelow, sibHash)
		return
	}

	return
}

// undoDeletion undo-es all the deletions that are passed in. The deletions that happened
// should be done in a single modify.
func (m *MapPollard) undoDeletion(createIndex []uint32, proof Proof, hashes []Hash) error {
	ingestIns, _, undoInfo, _, err := calculateHashes2(m.NumLeaves, hashes, proof)
	if err != nil {
		return err
	}

	for undoInfo.length() > 0 {
		updateHashInfo, insertDelInfo := undoInfo.pop()
		if updateHashInfo != nil {
			if updateHashInfo.isRoot {
				tree, _, _, err := DetectOffset(updateHashInfo.rootPos, m.NumLeaves)
				if err != nil {
					return err
				}

				if m.Roots[tree] != empty {
					return fmt.Errorf("expected to find empty root at pos %v but got %v",
						updateHashInfo.rootPos, m.Roots[tree])
				}
				m.Roots[tree] = updateHashInfo.origHash
				rootNode := Node{Remember: m.Full, AddIndex: -1}
				m.Nodes.Put(updateHashInfo.origHash, rootNode)
			} else {
				err := m.updateHash(updateHashInfo.curHash, updateHashInfo.origHash)
				if err != nil {
					return err
				}
			}
		} else {
			prevSibNode, curSib, aNode, curSibHash, found, err := m.fetchNodeForDel(insertDelInfo.sibHash)
			if err != nil {
				return err
			}
			if !found {
				continue
			}

			pNode := Node{Remember: m.Full, above: prevSibNode.above, AddIndex: -1}

			if prevSibNode.isRoot() {
				idx := slices.Index(m.Roots, insertDelInfo.sibHash)
				if idx == -1 {
					return fmt.Errorf("prevSib of %v is a root but is not found in roots",
						insertDelInfo.sibHash)
				}

				m.Roots[idx] = insertDelInfo.pHash

				prevHashNode := Node{Remember: m.Full, above: insertDelInfo.pHash}
				prevSibNode, prevHashNode, err = m.giveBelow(prevSibNode, prevHashNode, insertDelInfo.prevHash)
				if err != nil {
					return err
				}
				prevSibNode.above = insertDelInfo.pHash

				if insertDelInfo.isLeft {
					pNode.lBelow = insertDelInfo.prevHash
					pNode.rBelow = insertDelInfo.sibHash
				} else {
					pNode.lBelow = insertDelInfo.sibHash
					pNode.rBelow = insertDelInfo.prevHash
				}

				m.Nodes.Put(insertDelInfo.pHash, pNode)
				m.Nodes.Put(insertDelInfo.sibHash, prevSibNode)
				m.Nodes.Put(insertDelInfo.prevHash, prevHashNode)
				continue
			}

			// Move the prevSibNode down.
			prevSibNode, pNode, err = m.giveBelow(prevSibNode, pNode, insertDelInfo.pHash)
			if err != nil {
				return err
			}
			prevSibNode.above = curSibHash

			if aNode.lBelow == insertDelInfo.sibHash {
				aNode.lBelow = insertDelInfo.pHash
			} else if aNode.rBelow == insertDelInfo.sibHash {
				aNode.rBelow = insertDelInfo.pHash
			} else {
				return fmt.Errorf("%v not found. aNode %v points to l %v, r %v",
					insertDelInfo.sibHash, curSib.above, aNode.lBelow, aNode.rBelow)
			}

			prevHashNode := Node{
				Remember: m.Full,
				above:    curSibHash,
			}
			curSib, prevHashNode, err = m.giveBelow(curSib, prevHashNode, insertDelInfo.prevHash)
			if err != nil {
				return err
			}

			if insertDelInfo.isLeft {
				curSib.lBelow = insertDelInfo.prevHash
				curSib.rBelow = insertDelInfo.sibHash
			} else {
				curSib.lBelow = insertDelInfo.sibHash
				curSib.rBelow = insertDelInfo.prevHash
			}

			m.Nodes.Put(pNode.above, aNode)
			m.Nodes.Put(curSibHash, curSib)
			m.Nodes.Put(insertDelInfo.pHash, pNode)
			m.Nodes.Put(insertDelInfo.sibHash, prevSibNode)
			m.Nodes.Put(insertDelInfo.prevHash, prevHashNode)
		}
	}

	err = m.ingest(ingestIns)
	if err != nil {
		return err
	}

	for i, index := range createIndex {
		hash := hashes[i]
		node, found := m.Nodes.Get(hash)
		if !found {
			return fmt.Errorf("expected to find %v but didn't", hash)
		}

		node.AddIndex = int32(index)
		m.Nodes.Put(hash, node)
	}

	return nil
}

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
func (m *MapPollard) UndoWithTTLs(adds []Hash, createIndex []uint32,
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

	err = m.undoAdd(adds, s.Roots)
	if err != nil {
		return fmt.Errorf("Undo errored while undoing added leaves. %v", err)
	}

	err = m.undoDeletion(createIndex, proof, hashes)
	if err != nil {
		return fmt.Errorf("Undo errored while undoing deleted leaves. %v", err)
	}

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

	err = m.undoAdd(adds, s.Roots)
	if err != nil {
		return fmt.Errorf("Undo errored while undoing added leaves. %v", err)
	}

	err = m.undoDeletion(nil, proof, hashes)
	if err != nil {
		return fmt.Errorf("Undo errored while undoing deleted leaves. %v", err)
	}

	return nil
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

	var err error
	origTargets := make([]uint64, len(proveHashes))
	for i := range origTargets {
		n, _ := m.Nodes.Get(proveHashes[i])
		origTargets[i], err = m.calculatePosition(proveHashes[i], n)
		if err != nil {
			return Proof{}, err
		}
	}

	// Sort targets first. Copy to avoid mutating the original.
	targets := copySortedFunc(origTargets, uint64Cmp)

	// The positions of the hashes we need to prove the passed in targets.
	proofPos, _ := ProofPositions(targets, m.NumLeaves, m.TotalRows)

	// Go through all the needed positions and grab the hashes for them.
	// If the node doesn't exist, check that it's calculateable. If it is,
	// calculate it. If it isn't, return an error.
	hashes := make([]Hash, 0, len(proofPos))
	for i := range proofPos {
		pos := proofPos[i]
		hash, _, _, _, err := m.getNode(pos)
		if err != nil {
			// Should never happen. This means that there's something wrong with the
			// implementation since we've already checked that the proof for the leaf
			// exists.
			return Proof{}, fmt.Errorf("Proof position %v not cached for the requested "+
				"target slice of: %v\nproveHashes:\n%s\nneededPositions:%v\n",
				pos, origTargets, printHashes(proveHashes), proofPos)
		}

		hashes = append(hashes, hash)
	}

	return Proof{Targets: origTargets, Proof: hashes}, nil
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
		hash := m.GetHash(pos)
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
	return m.Verify(delHashes, Proof{origTargets, allProofHashes}, remember)
}

// GetMissingPositions returns all the missing positions that are needed to verify the given
// targets.
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
		h, _, _, _, _ := m.getNode(pos)
		if h == empty {
			missingPositions = append(missingPositions, pos)
		}
	}

	return missingPositions
}

// Verify returns an error if the given proof and the delHashes do not hash up to the stored roots.
// Passing the remember flag as true will cause the proof to be cached.
func (m *MapPollard) Verify(delHashes []Hash, proof Proof, remember bool) error {
	//m.rwLock.Lock()
	//defer m.rwLock.Unlock()

	ingestIns, _, _, rootCandidates, err := calculateHashes2(m.NumLeaves, delHashes, proof)
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

	ingestIns, _, _, _, err := calculateHashes2(m.NumLeaves, delHashes, proof)
	if err != nil {
		return err
	}

	return m.ingest(ingestIns)
}

// Ingest places the proof in the tree and remembers them.
//
// NOTE: there's no verification done that the passed in proof is valid. It's the
// caller's responsibility to verify that the given proof is valid.
//
// This function is different from Ingest() in that it's not safe for concurrent access.
func (m *MapPollard) ingest(ins IngestInstruction) error {
	if len(ins.Hashes)%3 != 0 {
		return fmt.Errorf("ingest hash length of %v is malformed as "+
			"it's not divisible by 3", len(ins.Hashes))
	}

	for i := len(ins.Hashes) - 1; i >= 0; i-- {
		hash := ins.Hashes[i]
		rBelow := ins.Hashes[i-1]
		lBelow := ins.Hashes[i-2]

		node, found := m.Nodes.Get(hash)
		if !found {
			return fmt.Errorf("node hash %v not found", hash)
		}

		if node.rBelow != empty {
			i--
			i--
			continue
		}

		node.lBelow = lBelow
		node.rBelow = rBelow
		m.Nodes.Put(hash, node)

		rNode := Node{
			Remember: ins.isLeaf[i],
			above:    hash,
			AddIndex: -1,
		}
		m.Nodes.Put(rBelow, rNode)

		lNode := Node{
			Remember: ins.isLeaf[i],
			above:    hash,
			AddIndex: -1,
		}
		m.Nodes.Put(lBelow, lNode)

		i--
		i--
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

		aNode.rBelow = empty
		aNode.lBelow = empty
		m.Nodes.Put(node.above, aNode)

		err = m.maybeForget(node.above)
		if err != nil {
			return err
		}
	}

	return nil
}

// getRoots returns the hashes of the roots.
func (m *MapPollard) GetRoots() []Hash {
	roots, _ := m.getRoots()
	return roots
}

// getRoots returns the root hashes and their positions.
//
// This function is different from GetRoots() in that it's not safe for concurrent access.
func (m *MapPollard) getRoots() ([]Hash, []uint64) {
	roots := make([]Hash, len(m.Roots))
	copy(roots, m.Roots)
	rootPositions := RootPositions(m.NumLeaves, m.TotalRows)

	return roots, rootPositions
}

// GetHash returns the hash for the given position. Empty hash (all values are 0) is returned
// if the given position is not cached.
func (m *MapPollard) GetHash(pos uint64) Hash {
	if m.TotalRows != TreeRows(m.NumLeaves) {
		pos = translatePos(pos, TreeRows(m.NumLeaves), m.TotalRows)
	}

	hash, _, _, _, _ := m.getNode(pos)
	return hash
}

func (m *MapPollard) fetchNode(hash Hash) *Node {
	node, found := m.Nodes.Get(hash)
	if !found {
		return nil
	}

	return &node
}

// getNode returns the node, it's sibling, and the parent of the given position.
func (m *MapPollard) getNode(pos uint64) (nHash Hash, n, sibling, parent *Node, err error) {
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
	n, sibling, parent = m.fetchNode(m.Roots[tree]), m.fetchNode(m.Roots[tree]), nil
	nHash = m.Roots[tree]

	if n == &emptyNode {
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
			nHash = n.lBelow
			n, sibling = m.fetchNode(n.lBelow), m.fetchNode(n.rBelow)
		} else {
			nHash = n.rBelow
			n, sibling = m.fetchNode(n.rBelow), m.fetchNode(n.lBelow)
		}

		// Return early if the path to the node we're looking for
		// doesn't exist.
		if n == nil {
			return Hash{}, nil, nil, nil, nil
		}
	}

	return
}

func (m *MapPollard) calculatePosition(hash Hash, node Node) (uint64, error) {
	// Tells whether to follow the left child or the right child when going
	// down the tree. 0 means left, 1 means right.
	leftRightIndicator := uint64(0)

	rowsToTop := 0
	for node.above != empty {
		aboveNode, found := m.Nodes.Get(node.above)
		if !found {
			return 0, fmt.Errorf("node %v points to above node of %v "+
				"but it's not found", hash, node.above)
		}

		if aboveNode.lBelow == hash {
			// Left
			leftRightIndicator <<= 1
		} else {
			// Right
			leftRightIndicator <<= 1
			leftRightIndicator |= 1
		}

		hash = node.above
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

// getLeafPosition returns the position of the leaf for the given hash and returns false
// if the leaf hash doesn't exist.
//
// MUST be called with the lock held.
func (m *MapPollard) getLeafHashPosition(hash Hash) (uint64, bool) {
	node, found := m.Nodes.Get(hash)
	if !found {
		return 0, false
	}
	if node.AddIndex == -1 {
		return 0, false
	}

	pos, err := m.calculatePosition(hash, node)
	if err != nil {
		return 0, false
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

	for _, rootHash := range rootHashes {
		m.Nodes.Put(rootHash, Node{AddIndex: -1})
		m.Roots = append(m.Roots, rootHash)
	}

	return m
}

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
	if n.lBelow != empty && n.rBelow != empty {
		wroteBytes, err := w.Write([]byte{1})
		if err != nil {
			return totalBytes, err
		}
		totalBytes += wroteBytes

		lNode, found := m.Nodes.Get(n.lBelow)
		if !found {
			return totalBytes, fmt.Errorf("lBelow of %v not found", n.lBelow)
		}

		leftBytes, err := m.writeOne(n.lBelow, lNode, w)
		if err != nil {
			return totalBytes, err
		}
		totalBytes += leftBytes

		rNode, found := m.Nodes.Get(n.rBelow)
		if !found {
			return totalBytes, fmt.Errorf("lBelow of %v not found", n.lBelow)
		}
		rightBytes, err := m.writeOne(n.rBelow, rNode, w)
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
func (m *MapPollard) readOne(above Hash, r io.Reader) (int64, Hash, error) {
	totalBytes := int64(0)

	var hash Hash
	node := Node{above: above}

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
		node.lBelow = lHash

		rightBytes, rHash, err := m.readOne(hash, r)
		if err != nil {
			return totalBytes, hash, err
		}
		totalBytes += rightBytes
		node.rBelow = rHash
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

	numRoots := uint8(buf[0])
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
