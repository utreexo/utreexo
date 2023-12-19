package utreexo

import (
	"encoding/binary"
	"fmt"
	"io"
	"sort"

	"golang.org/x/exp/slices"
)

// Assert that MapPollard implements the Utreexo interface.
var _ Utreexo = (*MapPollard)(nil)

// MapPollard is an implementation of the utreexo accumulators that supports pollard
// functionality.
type MapPollard struct {
	// CachedLeaves are the positions of the leaves that we always have cached.
	CachedLeaves map[Hash]uint64

	// Nodes are the leaves in the accumulator. The hashes are mapped to their
	// position in the accumulator.
	Nodes map[uint64]Leaf

	// NumLeaves are the number of total additions that have happened in the
	// accumulator.
	NumLeaves uint64

	// TotalRows is the number of rows the accumulator has allocated for.
	TotalRows uint8
}

// NewMapPollard returns a MapPollard with the nodes map initialized.
// NOTE: The default total rows is set to 50. This avoids costly remapping.
// For printing out the pollard for debugging purposes, set TotalRows 0 for
// pretty printing.
func NewMapPollard() MapPollard {
	return MapPollard{
		CachedLeaves: make(map[Hash]uint64),
		Nodes:        make(map[uint64]Leaf),
		TotalRows:    50,
	}
}

// Modify takes in the additions and deletions and updates the accumulator accordingly.
func (m *MapPollard) Modify(adds []Leaf, delHashes []Hash, proof Proof) error {
	err := m.remove(proof, delHashes)
	if err != nil {
		return err
	}

	err = m.add(adds)
	if err != nil {
		return err
	}

	return nil
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
	for _, add := range adds {
		// Add to the accumulator.
		err := m.addSingle(add)
		if err != nil {
			return err
		}

		m.NumLeaves++
	}

	return nil
}

// niecesPresent returns if either of the nieces exist for the given position.
func (m *MapPollard) niecesPresent(pos uint64) bool {
	if detectRow(pos, m.TotalRows) == 0 {
		return false
	}

	lNiecePos := leftChild(sibling(pos), m.TotalRows)
	rNiecePos := rightChild(sibling(pos), m.TotalRows)
	_, lNieceFound := m.Nodes[lNiecePos]
	_, rNieceFound := m.Nodes[rNiecePos]

	return lNieceFound || rNieceFound
}

// prunePosition prunes the node and its sibling at the given position if:
// 1: the position isn't a root.
// 2: it and its sibling aren't marked as remembered.
//
// NOTE: prunePosition will prune roots as well (needed for undo). The caller
// must check that roots aren't pruned.
func (m *MapPollard) prunePosition(pos uint64) {
	node := m.Nodes[pos]
	sibNode := m.Nodes[sibling(pos)]

	// Remove the node if:
	// 1: if either of the nodes aren't marked to be remembered.
	// 2: if either of the nieces for the given node aren't present.
	if !node.Remember && !sibNode.Remember {
		if !m.niecesPresent(sibling(pos)) {
			delete(m.Nodes, sibling(pos))
		}

		if !m.niecesPresent(pos) {
			delete(m.Nodes, pos)
		}
	}
}

// pruneNieces prunes the nieces of the given position if they are not needed.
func (m *MapPollard) pruneNieces(pos uint64) {
	if detectRow(pos, m.TotalRows) == 0 {
		return
	}
	lChild := leftChild(pos, m.TotalRows)

	m.prunePosition(lChild)
}

// forgetUnneededDel prunes the unneeded positions after the deletion of the passed in position.
func (m *MapPollard) forgetUnneededDel(del uint64) error {
	// We never need to forget the root. Can break early here.
	if isRootPositionTotalRows(del, m.NumLeaves, m.TotalRows) {
		return nil
	}

	parentPos := del

	// On each row, we determine if myself or my sibling still needs to be remembered.
	//
	// The cases in which myself needs to be remembered are:
	// 1: My sibling is to be remembered.
	// 2: I have nieces.
	//
	// The cases in which my sibling needs to be remembered are:
	// 1: Myself needs to be remembered.
	// 2: My sibling as nieces.
	for row := detectRow(del, m.TotalRows); row <= m.TotalRows; row++ {
		parentPos = parent(parentPos, m.TotalRows)

		// Break if we're on a root.
		if isRootPositionTotalRows(parentPos, m.NumLeaves, m.TotalRows) {
			break
		}

		// Prune the parentPos and its sibling.
		m.prunePosition(parentPos)
	}

	return nil
}

// addSingle adds one leaf to the accumulator.  If the remember field is set to true, the leaf
// will be cached.
func (m *MapPollard) addSingle(add Leaf) error {
	totalRows, err := m.remap()
	if err != nil {
		return err
	}

	position := m.NumLeaves
	pNode := add

	m.Nodes[position] = Leaf{Hash: add.Hash, Remember: add.Remember}
	if add.Remember {
		m.CachedLeaves[add.Hash] = position
	}

	for h := uint8(0); (m.NumLeaves>>h)&1 == 1; h++ {
		rootPos := rootPosition(m.NumLeaves, h, totalRows)
		node, ok := m.Nodes[rootPos]
		if !ok {
			return fmt.Errorf("Add fail. Didn't find root at %d. NumLeaves %d",
				rootPos, m.NumLeaves)
		}

		// If the root is empty, then we move up the current node and all its children.
		if node.Hash == empty {
			// Move up the current node.
			delete(m.Nodes, position)
			if add.Remember && pNode.Hash == add.Hash {
				_, exists := m.CachedLeaves[add.Hash]
				if exists {
					m.CachedLeaves[add.Hash] = parent(position, totalRows)
				}
			}

			// Move up the children. Have to give it +1 with the numleaves as we need
			// them to move up to the positions after the add.
			err = m.moveUpDescendants(position, rootPos, m.NumLeaves+1)
			if err != nil {
				return err
			}
		} else {
			pNode = Leaf{Hash: parentHash(node.Hash, pNode.Hash)}
		}

		position = parent(position, totalRows)
		m.Nodes[position] = pNode
		m.pruneNieces(position)
	}

	return nil
}

// moveUpDescendants calculates the new positions for the children of the given position
// and re-inserts them into the map of nodes with their new positions. The function
// recursively moves up children this until the bottom-most row.
func (m *MapPollard) moveUpDescendants(position, delPos, numLeaves uint64) error {
	row := int(detectRow(position, m.TotalRows))
	if row == 0 {
		return nil
	}

	toMoveUp := []uint64{position, sibling(position)}
	slices.Sort(toMoveUp)

	next := make([]uint64, 0, len(toMoveUp)*2)
	for h := row; h >= 0; h-- {
		for i := range toMoveUp {
			nextChildren, err := m.moveUpNieces(toMoveUp[i], delPos, numLeaves)
			if err != nil {
				return err
			}

			next = mergeSortedSlicesFunc(next, nextChildren, uint64Cmp)
		}

		toMoveUp = next
		next = next[:0]
	}

	return nil
}

// moveUpNieces moves up the nieces of the given position.
func (m *MapPollard) moveUpNieces(position, delPos, numLeaves uint64) ([]uint64, error) {
	row := detectRow(position, m.TotalRows)
	if row == 0 {
		return nil, nil
	}

	l, err := m.moveUpChild(sibling(position), delPos, numLeaves, leftChild)
	if err != nil {
		return nil, err
	}
	r, err := m.moveUpChild(sibling(position), delPos, numLeaves, rightChild)
	if err != nil {
		return nil, err
	}

	l = append(l, r...)
	return l, nil
}

// moveUpChild moves up the children of the given position to what their next position would
// be after delPos has been deleted.
func (m *MapPollard) moveUpChild(position, delPos, numLeaves uint64,
	child func(uint64, uint8) uint64) ([]uint64, error) {

	c := child(sibling(position), m.TotalRows)
	nextPos, err := calcNextPosition(c, delPos, m.TotalRows)
	if err != nil {
		return nil, err
	}

	lVal, found := m.Nodes[c]
	if found {
		delete(m.Nodes, c)
		m.Nodes[nextPos] = lVal

		_, exists := m.CachedLeaves[lVal.Hash]
		if exists {
			m.CachedLeaves[lVal.Hash] = nextPos
		}

		return []uint64{c}, nil
	}

	return []uint64{c}, nil
}

// remap moves up the positions of nodes that aren't at row 0 whenever the accumulator grows.
// Returns the total number of rows needed to house numleaves+1 amount of leaves.
func (m *MapPollard) remap() (uint8, error) {
	nextRows := treeRows(m.NumLeaves + 1)
	if nextRows <= m.TotalRows {
		return m.TotalRows, nil
	}

	// Go through all the possible positions from rows 1 to total rows and
	// move them up.
	//
	// We do this as it's not possible to iter and modify a map when we're
	// modifying the keys.
	for h := uint8(1); h <= m.TotalRows; h++ {
		startPos := startPositionAtRow(h, m.TotalRows)
		maxPos, err := maxPositionAtRow(h, m.TotalRows, m.NumLeaves)
		if err != nil {
			return 0, err
		}

		j := startPositionAtRow(h, nextRows)
		for i := startPos; i <= maxPos; i++ {
			hash, found := m.Nodes[i]
			if found {
				delete(m.Nodes, i)
				m.Nodes[j] = hash
			}

			j++
		}
	}

	// Go through the entire cached leaves and recalculate the proof positions.
	// For cached leaves, looping through the map and modifying it is ok since
	// only the values are modified.
	for k, v := range m.CachedLeaves {
		newPos := translatePos(v, m.TotalRows, nextRows)
		m.CachedLeaves[k] = newPos
	}

	m.TotalRows = nextRows
	return nextRows, nil
}

// uncacheLeaves uncaches the dels from the slice of cache leaves. It does not modify
// the map of nodes.
func (m *MapPollard) uncacheLeaves(dels []Hash) {
	for _, del := range dels {
		delete(m.CachedLeaves, del)
	}
}

// cached checks if the given hashes are cached.
func (m *MapPollard) cached(hashes []Hash) bool {
	for _, hash := range hashes {
		_, found := m.CachedLeaves[hash]
		if !found {
			return found
		}
	}

	return true
}

// forgetBelow removes all the positions that are descendants of the given position.
func (m *MapPollard) forgetBelow(position uint64) {
	row := detectRow(position, m.TotalRows)
	if row == 0 {
		return
	}

	l := leftChild(position, m.TotalRows)
	r := sibling(l)

	delete(m.Nodes, l)
	delete(m.Nodes, r)

	m.forgetBelow(l)
	m.forgetBelow(r)
}

// updateHashes updates the hashes of the upper nodes of the given position.
func (m *MapPollard) updateHashes(position uint64, hash Hash) {
	node := Leaf{Hash: hash}

	pos := parent(position, m.TotalRows)
	for row := detectRow(pos, m.TotalRows); row <= m.TotalRows; row++ {
		sibPos := sibling(pos)
		sibNode := m.Nodes[sibPos]

		if isLeftNiece(pos) {
			node.Hash = parentHash(node.Hash, sibNode.Hash)
		} else {
			node.Hash = parentHash(sibNode.Hash, node.Hash)
		}

		pos = parent(pos, m.TotalRows)

		// Update the parent hash if we have it cached.
		_, found := m.Nodes[pos]
		if found {
			m.Nodes[pos] = node
		}

		if isRootPositionTotalRows(pos, m.NumLeaves, m.TotalRows) {
			break
		}
	}
}

// removeSingle removes the given position and updates relevant hashes all the way
// up to the root.
func (m *MapPollard) removeSingle(del uint64) error {
	// Forget my children and my children's children.
	m.forgetBelow(del)

	// If it's a root, then mark it as empty and skip other operations.
	if isRootPositionTotalRows(del, m.NumLeaves, m.TotalRows) {
		m.Nodes[del] = Leaf{Hash: empty}
		return nil
	}

	// Delete myself.
	delete(m.Nodes, del)

	// Move up my sibling.
	node, found := m.Nodes[sibling(del)]
	if found {
		delete(m.Nodes, sibling(del))
		m.Nodes[parent(del, m.TotalRows)] = node

		// Update the cache position if it exists in there.
		_, cacheFound := m.CachedLeaves[node.Hash]
		if cacheFound {
			newPos, err := calcNextPosition(sibling(del), del, m.TotalRows)
			if err != nil {
				return err
			}
			m.CachedLeaves[node.Hash] = newPos
			node.Remember = true
		}

		// Move up all descendants of my sibling.
		err := m.moveUpDescendants(sibling(del), del, m.NumLeaves)
		if err != nil {
			return err
		}
	}

	m.updateHashes(del, node.Hash)

	m.forgetUnneededDel(del)

	return nil
}

// remove removes the targets and the delHashes from the accumulator. The del targets
// and hashes do not have to be in the same order.
//
// NOTE: dels MUST be sorted.
func (m *MapPollard) remove(proof Proof, delHashes []Hash) error {
	// Check first that we have all the necessary nodes for deletion.
	if !m.cached(delHashes) {
		return fmt.Errorf("Cannot delete:\n%s\nas not all of them are cached",
			printHashes(delHashes))
	}

	// Remove dels from the cached leaves.
	m.uncacheLeaves(delHashes)

	detwinedDels := copySortedFunc(proof.Targets, uint64Less)
	if m.TotalRows != treeRows(m.NumLeaves) {
		detwinedDels = translatePositions(detwinedDels, treeRows(m.NumLeaves), m.TotalRows)
	}

	detwinedDels = deTwin(detwinedDels, m.TotalRows)
	for _, del := range detwinedDels {
		m.removeSingle(del)
	}
	return nil
}

// undoSingleAdd undo-s the last single addition and will put back empty roots that were
// written over.
func (m *MapPollard) undoSingleAdd(emptyRootPositions []uint64) ([]uint64, error) {
	row := getLowestRoot(m.NumLeaves, m.TotalRows)
	pos := rootPosition(m.NumLeaves-1, row, m.TotalRows)
	lChild := leftChild(pos, m.TotalRows)

	for h := int(row); h >= 0; h-- {
		leaf, found := m.Nodes[pos]
		if found {
			delete(m.Nodes, pos)
			delete(m.CachedLeaves, leaf.Hash)
		}

		if h != 0 {
			if len(emptyRootPositions) > 0 &&
				emptyRootPositions[0] == lChild {

				err := m.placeEmptyRoot(lChild)
				if err != nil {
					return emptyRootPositions, err
				}
				emptyRootPositions = emptyRootPositions[1:]

				m.Nodes[lChild] = Leaf{Hash: empty, Remember: true}
			}
		}

		pos = rightChild(pos, m.TotalRows)
		lChild = leftChild(pos, m.TotalRows)
	}

	m.NumLeaves--

	return emptyRootPositions, nil
}

// placeEmptyRoot will put back the empty root at the given previous root position and
// move down the nodes that are at the current empty root position.
func (m *MapPollard) placeEmptyRoot(prevRootPos uint64) error {
	sib := sibling(prevRootPos)
	row := detectRow(sib, m.TotalRows)

	for h := int(row); h > 0; h-- {
		child, err := childMany(sib, uint8(h), m.TotalRows)
		if err != nil {
			return err
		}

		for i := 0; i < 1<<h; i++ {
			pos := uint64(i) + child

			curPos, err := calcNextPosition(pos, prevRootPos, m.TotalRows)
			if err != nil {
				return err
			}

			v, found := m.Nodes[curPos]
			if found && v.Hash != empty {
				delete(m.Nodes, curPos)

				_, cached := m.CachedLeaves[v.Hash]
				if cached {
					v.Remember = true
					m.CachedLeaves[v.Hash] = pos
				}
				m.Nodes[pos] = v
			}
		}
	}

	return nil
}

// undoDeletion undo-es all the deletions that are passed in. The deletions that happened
// should be done in a single modify.
func (m *MapPollard) undoDeletion(proof Proof, hashes []Hash) error {
	// Sort and translate the positions if needed.
	hnp := toHashAndPos(proof.Targets, hashes)
	if treeRows(m.NumLeaves) != m.TotalRows {
		hnp.positions = translatePositions(hnp.positions, treeRows(m.NumLeaves), m.TotalRows)
		sort.Sort(hnp)
	}

	// Make separate detwined targets.
	deTwinedTargets := make([]uint64, len(hnp.positions))
	copy(deTwinedTargets, hnp.positions)
	deTwinedTargets = deTwin(deTwinedTargets, m.TotalRows)

	// Go through the detwined targets in descending order and move down the nodes
	// that have moved up from the deletion.
	for i := len(deTwinedTargets) - 1; i >= 0; i-- {
		// If the sibling of the target exists in the accumulator, move it down by
		// placing an empty position at the given target.
		if inForest(sibling(deTwinedTargets[i]), m.NumLeaves, m.TotalRows) {
			err := m.placeEmptyRoot(deTwinedTargets[i])
			if err != nil {
				return err
			}
		}

		// Grab the former sibling in the parent position and move it down to its
		// previous position.
		sib := parent(deTwinedTargets[i], m.TotalRows)
		prevPos := calcPrevPosition(sib, deTwinedTargets[i], m.TotalRows)
		v, found := m.Nodes[sib]
		if found {
			_, cached := m.CachedLeaves[v.Hash]
			if cached {
				m.CachedLeaves[v.Hash] = prevPos
				v.Remember = true
			}

			delete(m.Nodes, sib)
			m.Nodes[prevPos] = v
		}
	}

	// Calculate the positions of the proofs and translate them if needed and
	// then place in the proof hashes into the calculated positions.
	sortedTargets := copySortedFunc(proof.Targets, uint64Less)
	proofPos, _ := proofPositions(sortedTargets, m.NumLeaves, treeRows(m.NumLeaves))
	if treeRows(m.NumLeaves) != m.TotalRows {
		proofPos = m.trimProofPos(proofPos, m.NumLeaves)
		proofPos = translatePositions(proofPos, treeRows(m.NumLeaves), m.TotalRows)
	}
	for i := range proofPos {
		pos := proofPos[i]
		_, found := m.Nodes[pos]
		if !found {
			m.Nodes[pos] = Leaf{Hash: proof.Proof[i]}
		}
	}

	// Calculate the previous hashes and their positions and translate them if needed.
	newhnp, _, err := calculateHashes(m.NumLeaves, hashes, proof)
	if err != nil {
		return err
	}
	if treeRows(m.NumLeaves) != m.TotalRows {
		newhnp.positions = translatePositions(newhnp.positions, treeRows(m.NumLeaves), m.TotalRows)
		sort.Sort(newhnp)
	}

	// Go through all the calculated positions and place them int the accumulator.
	for i, pos := range newhnp.positions {
		// If the position is a target, then set the remember to true.
		remember := false
		for _, target := range proof.Targets {
			if treeRows(m.NumLeaves) != m.TotalRows {
				translated := translatePos(target, treeRows(m.NumLeaves), m.TotalRows)
				if pos == translated {
					remember = true
				}
			} else {
				if pos == target {
					remember = true
				}
			}
		}
		m.Nodes[pos] = Leaf{Hash: newhnp.hashes[i], Remember: remember}

		// Only add it to the cached leaves if remember is true.
		if remember {
			m.CachedLeaves[newhnp.hashes[i]] = pos
		}
	}

	return nil
}

// getRootsAfterDel will place empty roots if the last deletion had deleted roots. It will not update
// the hashes themselves.
func (m *MapPollard) getRootsAfterDel(numAdds uint64, targets, prevRootPos []uint64, origPrevRoots []Hash) []Hash {
	prevRoots := make([]Hash, len(origPrevRoots))
	copy(prevRoots, origPrevRoots)

	detwined := deTwin(translatePositions(copySortedFunc(targets, uint64Less),
		treeRows(m.NumLeaves-numAdds), m.TotalRows), m.TotalRows)

	for i := range detwined {
		for j := range prevRootPos {
			if detwined[i] == prevRootPos[j] {
				prevRoots[j] = empty
			}
		}
	}

	return prevRoots
}

// getWrittenOverEmptyRoots returns the positions of the empty roots that have been written
// over after the addition to the accumulator.
func (m *MapPollard) getWrittenOverEmptyRoots(numAdds uint64, origTargets []uint64, origPrevRoots []Hash) ([]uint64, error) {
	prevRootPos := RootPositions(m.NumLeaves-numAdds, m.TotalRows)

	// Get the roots after the deletion has happened.
	prevRoots := m.getRootsAfterDel(numAdds, origTargets, prevRootPos, origPrevRoots)

	// Get the positions of empty roots that are written over after the add.
	destroyedPositions := rootsToDestory(numAdds, m.NumLeaves-numAdds, prevRoots)

	// Translate the positions if needed.
	if treeRows(m.NumLeaves) != m.TotalRows {
		destroyedPositions = translatePositions(destroyedPositions, treeRows(m.NumLeaves), m.TotalRows)
	}

	// Loop through all the previous roots and only add their position to the previous
	// empty root positions if it's been destroyed on the add.
	prevEmptyRootPos := make([]uint64, 0, len(prevRootPos))
	for i, root := range prevRoots {
		// Look for empty roots.
		if root == empty {
			// Only append the empty roots if they've been written over.
			for _, destroyed := range destroyedPositions {
				if destroyed == prevRootPos[i] {
					prevEmptyRootPos = append(prevEmptyRootPos, prevRootPos[i])
				}
			}
		}
	}

	return prevEmptyRootPos, nil
}

// undoAdd will remove the additions that had happened and will place empty roots back to where they were.
func (m *MapPollard) undoAdd(numAdds uint64, origTargets []uint64, origPrevRoots []Hash) error {
	// Get the previously empty roots positions that have been written over by the add.
	// These empty roots will be placed back into the accumulator.
	prevEmptyRootPos, err := m.getWrittenOverEmptyRoots(numAdds, origTargets, origPrevRoots)
	if err != nil {
		return err
	}

	for i := 0; i < int(numAdds); i++ {
		prevEmptyRootPos, err = m.undoSingleAdd(prevEmptyRootPos)
		if err != nil {
			return err
		}
	}

	return err
}

// Undo will undo the last modify. The numAdds, proof, hashes, MUST be the data from the previous modify.
// The origPrevRoots MUST be the roots that this Undo will go back to.
func (m *MapPollard) Undo(numAdds uint64, proof Proof, hashes, origPrevRoots []Hash) error {
	err := m.undoAdd(numAdds, proof.Targets, origPrevRoots)
	if err != nil {
		return err
	}

	err = m.undoDeletion(proof, hashes)
	if err != nil {
		return err
	}

	_, rootPos := m.getRoots()
	for i := range rootPos {
		var remember bool
		_, found := m.CachedLeaves[origPrevRoots[i]]
		if found {
			remember = true
		}
		m.Nodes[rootPos[i]] = Leaf{Hash: origPrevRoots[i], Remember: remember}
	}

	return nil
}

// Prove returns a proof of all the targets that are passed in.
// TODO: right now it refuses to prove anything but the explicitly cached leaves.
// There may be some leaves that it could prove that's not cached due to the proofs
// overlapping.
func (m *MapPollard) Prove(proveHashes []Hash) (Proof, error) {
	// Check that the targets are proveable.
	if !m.cached(proveHashes) {
		return Proof{}, fmt.Errorf("Cannot prove:\n%s\nas not all of them are cached",
			printHashes(proveHashes))
	}

	origTargets := make([]uint64, len(proveHashes))
	for i := range origTargets {
		origTargets[i] = m.CachedLeaves[proveHashes[i]]
	}

	// Sort targets first. Copy to avoid mutating the original.
	targets := copySortedFunc(origTargets, uint64Less)

	// The positions of the hashes we need to prove the passed in targets.
	proofPos, _ := proofPositions(targets, m.NumLeaves, m.TotalRows)

	// Go through all the needed positions and grab the hashes for them.
	// If the node doesn't exist, check that it's calculateable. If it is,
	// calculate it. If it isn't, return an error.
	hashes := make([]Hash, 0, len(proofPos))
	for i := range proofPos {
		pos := proofPos[i]
		node, ok := m.Nodes[pos]
		if !ok {
			// Should never happen. This means that there's something wrong with the
			// implementation since we've already checked that the proof for the leaf
			// exists.
			return Proof{}, fmt.Errorf("Proof position %v not cached for the requested "+
				"target slice of: %v\nproveHashes:\n%s\nneededPositions:%v\n",
				pos, origTargets, printHashes(proveHashes), proofPos)
		}

		hashes = append(hashes, node.Hash)
	}

	// If the map pollard is set with higher rows than what's actually needed,
	// translate the positions.
	if m.TotalRows != treeRows(m.NumLeaves) {
		for i := range origTargets {
			origTargets[i] = translatePos(origTargets[i], m.TotalRows, treeRows(m.NumLeaves))
		}
	}

	return Proof{Targets: origTargets, Proof: hashes}, nil
}

// VerifyPartialProof takes partial proof of the targets and attempts to prove their existence.
// If the remember bool is false, the accumulator is not modified. If it is true, the necessary
// hashes to prove the targets are cached.
//
// NOTE: proofHashes MUST be sorted in relation to their positions in the accumulator.
func (m *MapPollard) VerifyPartialProof(origTargets []uint64, delHashes, proofHashes []Hash, remember bool) error {
	// Sort targets first. Copy to avoid mutating the original.
	targets := copySortedFunc(origTargets, uint64Less)

	// Figure out what hashes at which positions are needed.
	proofPositions, _ := proofPositions(targets, m.NumLeaves, treeRows(m.NumLeaves))

	// Translate the proof positions if needed.
	if treeRows(m.NumLeaves) != m.TotalRows {
		proofPositions = translatePositions(proofPositions, treeRows(m.NumLeaves), m.TotalRows)
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
	// Sort targets first. Copy to avoid mutating the original.
	targets := copySortedFunc(origTargets, uint64Less)

	// Generate the positions needed to prove this.
	proofPos, _ := proofPositions(targets, m.NumLeaves, treeRows(m.NumLeaves))
	if treeRows(m.NumLeaves) != m.TotalRows {
		proofPos = translatePositions(proofPos, treeRows(m.NumLeaves), m.TotalRows)
	}

	// Go through all the proof positions and mark the ones that are missing.
	missingPositions := make([]uint64, 0, len(proofPos))
	for i := range proofPos {
		pos := proofPos[i]
		_, ok := m.Nodes[pos]
		if !ok {
			missingPositions = append(missingPositions, pos)
		}
	}

	if treeRows(m.NumLeaves) != m.TotalRows {
		missingPositions = translatePositions(missingPositions, m.TotalRows, treeRows(m.NumLeaves))
		missingPositions = m.trimProofPos(missingPositions, m.NumLeaves)
	}

	return missingPositions
}

// Verify returns an error if the given proof and the delHashes do not hash up to the stored roots.
// Passing the remember flag as true will cause the proof to be cached.
func (m *MapPollard) Verify(delHashes []Hash, proof Proof, remember bool) error {
	if treeRows(m.NumLeaves) != m.TotalRows {
		proof.Targets = translatePositions(proof.Targets, m.TotalRows, treeRows(m.NumLeaves))
	}

	s := m.GetStump()
	_, err := Verify(s, delHashes, proof)
	if err != nil {
		return err
	}

	if remember {
		m.Ingest(delHashes, proof)
	}

	return nil
}

// trimProofPos returns a slice of proof positions with the proof positions that
// aren't needed trimmed out.
//
// The given proof positions must be sorted.
func (m *MapPollard) trimProofPos(proofPos []uint64, numLeaves uint64) []uint64 {
	rows := treeRows(numLeaves)

	i := 0
	for ; i < len(proofPos); i++ {
		if !inForest(proofPos[i], numLeaves, rows) {
			break
		}
	}

	return proofPos[:i]
}

// Ingest places the proof in the tree and remembers them.
//
// NOTE: there's no verification done that the passed in proof is valid. It's the
// caller's responsibility to verify that the given proof is valid.
func (m *MapPollard) Ingest(delHashes []Hash, proof Proof) error {
	hnp := toHashAndPos(proof.Targets, delHashes)
	if m.TotalRows != treeRows(m.NumLeaves) {
		hnp.positions = translatePositions(hnp.positions, treeRows(m.NumLeaves), m.TotalRows)
		sort.Sort(hnp)
	}

	// Calculate and ingest the proof.
	proofPos, _ := proofPositions(hnp.positions, m.NumLeaves, m.TotalRows)
	if treeRows(m.NumLeaves) != m.TotalRows && len(proofPos) != len(proof.Proof) {
		proofPos = m.trimProofPos(proofPos, m.NumLeaves)
	}
	for i, pos := range proofPos {
		_, found := m.Nodes[pos]
		if !found {
			m.Nodes[pos] = Leaf{Hash: proof.Proof[i]}
		}
	}

	// Calculate the intermediate positions and their hashes.
	intermediate, _, err := calculateHashes(m.NumLeaves, delHashes, proof)
	if err != nil {
		return err
	}
	if m.TotalRows != treeRows(m.NumLeaves) {
		intermediate.positions = translatePositions(intermediate.positions, treeRows(m.NumLeaves), m.TotalRows)
		sort.Sort(intermediate)
	}

	// Ingest the targets and the intermediate positions and their hashes.
	for i, pos := range intermediate.positions {
		remember := false
		for i := range hnp.positions {
			if hnp.positions[i] == pos {
				remember = true
				break
			}
		}
		m.Nodes[pos] = Leaf{Hash: intermediate.hashes[i], Remember: remember}
		if remember {
			m.CachedLeaves[intermediate.hashes[i]] = pos
		}
	}

	return nil
}

// Prune prunes the passed in hashes and the proofs for them. Will not prune the proof if it's
// needed for another cached hash.
func (m *MapPollard) Prune(hashes []Hash) error {
	for _, hash := range hashes {
		pos, found := m.CachedLeaves[hash]
		if !found {
			continue
		}

		delete(m.CachedLeaves, hash)

		leaf, found := m.Nodes[pos]
		if !found {
			return fmt.Errorf("node map inconsistent as the hash %s was found"+
				"in the cache but not the node map", leaf.Hash)
		}

		// Mark the remember field as false and put that leaf in the map.
		leaf.Remember = false
		m.Nodes[pos] = leaf

		// Call prune positions until the root.
		for row := detectRow(pos, m.TotalRows); row <= treeRows(m.NumLeaves); row++ {
			// Break if we're on a root.
			if isRootPositionTotalRows(pos, m.NumLeaves, m.TotalRows) {
				break
			}
			m.prunePosition(pos)
			pos = parent(pos, m.TotalRows)
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
func (m *MapPollard) getRoots() ([]Hash, []uint64) {
	nRoots := numRoots(m.NumLeaves)

	roots := make([]Hash, 0, nRoots)
	rootPositions := RootPositions(m.NumLeaves, m.TotalRows)
	for _, rootPosition := range rootPositions {
		node := m.Nodes[rootPosition]
		roots = append(roots, node.Hash)
	}

	return roots, rootPositions
}

// GetHash returns the hash for the given position. Empty hash (all values are 0) is returned
// if the given position is not cached.
func (m *MapPollard) GetHash(pos uint64) Hash {
	return m.Nodes[pos].Hash
}

func (m *MapPollard) highestPos() uint64 {
	totalRows := treeRows(m.NumLeaves)
	pos := rootPosition(m.NumLeaves, totalRows, totalRows)
	return translatePos(pos, totalRows, m.TotalRows)
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
	return Stump{Roots: m.GetRoots(), NumLeaves: m.NumLeaves}
}

// Write writes the entire pollard to the writer.
func (m *MapPollard) Write(w io.Writer) (int, error) {
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

	// Write the count for the cache leaf elements in the map.
	binary.LittleEndian.PutUint64(buf[:], uint64(len(m.CachedLeaves)))
	bytes, err = w.Write(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += bytes

	// Write the map elements.
	for k, v := range m.CachedLeaves {
		written, err := w.Write(k[:])
		if err != nil {
			return totalBytes, err
		}
		totalBytes += written

		binary.LittleEndian.PutUint64(buf[:], v)
		bytes, err = w.Write(buf[:])
		if err != nil {
			return totalBytes, err
		}
		totalBytes += bytes
	}

	// Write the count for the node elements in the map.
	binary.LittleEndian.PutUint64(buf[:], uint64(len(m.Nodes)))
	bytes, err = w.Write(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += bytes

	// Write the node elements.
	var leafBuf [33]byte
	for k, v := range m.Nodes {
		binary.LittleEndian.PutUint64(buf[:], k)
		bytes, err := w.Write(buf[:])
		if err != nil {
			return bytes, err
		}
		totalBytes += bytes

		copy(leafBuf[:32], v.Hash[:])
		if v.Remember {
			leafBuf[32] = 1
		}
		bytes, err = w.Write(leafBuf[:])
		if err != nil {
			return bytes, err
		}
		totalBytes += bytes
	}

	return totalBytes, nil
}

// Read reads the pollard from the reader into the map pollard variable.
func (m *MapPollard) Read(r io.Reader) (int, error) {
	totalBytes := 0

	var buf [8]byte

	// Read the total rows.
	bytes, err := r.Read(buf[:1])
	if err != nil {
		return totalBytes, err
	}
	m.TotalRows = buf[0]
	totalBytes += bytes

	// Read the number of leaves.
	bytes, err = r.Read(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += bytes
	m.NumLeaves = binary.LittleEndian.Uint64(buf[:])

	// Read the count for the cache leaf elements in the map.
	bytes, err = r.Read(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += bytes
	numCachedLeaves := binary.LittleEndian.Uint64(buf[:])

	// Read elements and put them in the map.
	m.CachedLeaves = make(map[Hash]uint64, numCachedLeaves)
	var hash Hash
	for i := 0; i < int(numCachedLeaves); i++ {
		read, err := r.Read(hash[:])
		if err != nil {
			return totalBytes, err
		}
		totalBytes += read

		// Read the number of leaves.
		bytes, err = r.Read(buf[:])
		if err != nil {
			return totalBytes, err
		}
		totalBytes += bytes
		m.CachedLeaves[hash] = binary.LittleEndian.Uint64(buf[:])
	}

	// Read the count for the node elements in the map.
	bytes, err = r.Read(buf[:])
	if err != nil {
		return totalBytes, err
	}
	totalBytes += bytes
	nodeCount := binary.LittleEndian.Uint64(buf[:])

	m.Nodes = make(map[uint64]Leaf, nodeCount)
	var leafBuf [33]byte
	for i := 0; i < int(nodeCount); i++ {
		bytes, err := r.Read(buf[:])
		if err != nil {
			return bytes, err
		}
		totalBytes += bytes
		position := binary.LittleEndian.Uint64(buf[:])

		read, err := r.Read(leafBuf[:])
		if err != nil {
			return totalBytes, err
		}
		totalBytes += read

		var hash Hash
		copy(hash[:], leafBuf[:32])
		leaf := Leaf{Hash: hash, Remember: leafBuf[32] == 1}

		m.Nodes[position] = leaf

	}

	// Sanity check.
	leafHashes := make([]Hash, 0, len(m.CachedLeaves))
	for k, v := range m.CachedLeaves {
		leaf, found := m.Nodes[v]
		if !found {
			return totalBytes,
				fmt.Errorf("Corrupted pollard. Missing cached leaf at %d", v)
		}

		if k != leaf.Hash {
			return totalBytes,
				fmt.Errorf("Corrupted pollard. Pos %d cached hash: %s, but have %s",
					v, k, leaf.Hash)
		}

		leafHashes = append(leafHashes, k)
	}

	return totalBytes, nil
}
