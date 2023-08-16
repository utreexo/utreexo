package utreexo

import (
	"crypto/sha512"
	"encoding/hex"
	"fmt"
	"math"
	"math/bits"
	"sort"

	"golang.org/x/exp/slices"
)

// parentHash returns the hash of the left and right hashes passed in.
func parentHash(l, r Hash) Hash {
	h := sha512.New512_256()
	h.Write(l[:])
	h.Write(r[:])
	return *((*Hash)(h.Sum(nil)))
}

// leftChild gives you the position of the left child. The least significant
// bit will be 0.
func leftChild(position uint64, forestRows uint8) uint64 {
	mask := uint64(2<<forestRows) - 1
	return (position << 1) & mask
}

// rightChild gives you the position of the right child. The least significant
// bit will be 1.
func rightChild(position uint64, forestRows uint8) uint64 {
	mask := uint64(2<<forestRows) - 1
	return ((position << 1) & mask) | 1
}

// childMany returns the child that's multiple rows lower. The returned child is always of the left child.
// In the tree below, position=14, drop=3, forestRows=3 will return 00.
// Arg of: position=14, drop=2, forestRows=3 will return 08.
//
// 14
// |---------------\
// 12              13
// |-------\       |-------\
// 08      09      10      11
// |---\   |---\   |---\   |---\
// 00  01  02  03  04  05  06  07
func childMany(position uint64, drop, forestRows uint8) (uint64, error) {
	if drop == 0 {
		return position, nil
	}
	if drop > forestRows {
		return 0, fmt.Errorf("drop of %d is greater than forestRows of %d", drop, forestRows)
	}
	mask := uint64(2<<forestRows) - 1
	return (position << drop) & mask, nil
}

// sibling returns the sibling of this node.
func sibling(pos uint64) uint64 {
	return pos ^ 1
}

// leftSib returns the left sibling for this node. If the node is
// the left sibling, itself is returned.
func leftSib(pos uint64) uint64 {
	return pos &^ 1
}

// rightSib returns the right sibling for this node. If the node is
// the right sibling, itself is returned.
func rightSib(pos uint64) uint64 {
	return pos | 1
}

// parent returns the position of the parent of this position.
func parent(position uint64, forestRows uint8) uint64 {
	return (position >> 1) | (1 << forestRows)
}

// parentMany returns the position of the ancestor that's rise rows above the given position.
// rise=0 returns position, rise=1 returns the parent, rise=2 returns the grandparent.
func parentMany(position uint64, rise, forestRows uint8) (uint64, error) {
	if rise == 0 {
		return position, nil
	}
	if rise > forestRows {
		return 0, fmt.Errorf("Cannot rise more than the forestRows. "+
			"rise %d, forestRows %d", rise, forestRows)
	}
	mask := uint64(2<<forestRows) - 1
	return (position>>rise | (mask << uint64(forestRows-(rise-1)))) & mask, nil
}

// isLeftNiece returns if the position is located on the left.
func isLeftNiece(position uint64) bool {
	return position&1 == 0
}

// rootPosition retuns the position of the root at that row given a number of
// leaves, the row of the position, and the entire rows of the forest. Does not
// return an error if there's no root at that row.
func rootPosition(leaves uint64, h, forestRows uint8) uint64 {
	mask := uint64(2<<forestRows) - 1
	before := leaves & (mask << (h + 1))
	shifted := (before >> h) | (mask << (forestRows + 1 - h))
	return shifted & mask
}

// rootPositions returns all the rootPositions for the given numLeaves and totalRows.
func rootPositions(numLeaves uint64, totalRows uint8) []uint64 {
	nRoots := numRoots(numLeaves)
	rootPositions := make([]uint64, 0, nRoots)
	for h := int(totalRows); h >= 0; h-- {
		if !rootExistsOnRow(numLeaves, uint8(h)) {
			continue
		}

		rootPos := rootPosition(numLeaves, uint8(h), totalRows)
		rootPositions = append(rootPositions, rootPos)
	}

	return rootPositions
}

// isRootPositionTotalRows is a wrapper around isRootPosition that will translate the given
// position if needed.
func isRootPositionTotalRows(position, numLeaves uint64, totalRows uint8) bool {
	if totalRows != treeRows(numLeaves) {
		translated := translatePos(position, totalRows, treeRows(numLeaves))
		return isRootPosition(translated, numLeaves)
	}

	return isRootPosition(position, numLeaves)
}

// isRootPosition checks if the current position is a root given the number of
// leaves.
func isRootPosition(position, numLeaves uint64) bool {
	row := detectRow(position, treeRows(numLeaves))
	return isRootPositionOnRow(position, numLeaves, row)
}

// isRootPositionOnRow checks if the current position is a root given the number of
// leaves, current row, and the entire rows of the forest.
func isRootPositionOnRow(position, numLeaves uint64, row uint8) bool {
	rootPresent := numLeaves&(1<<row) != 0
	rootPos := rootPosition(numLeaves, row, treeRows(numLeaves))

	return rootPresent && rootPos == position
}

// isRootPositionOnRowTotalRows is a wrapper around isRootPositionOnRow that will translate the given
// position if needed.
func isRootPositionOnRowTotalRows(position, numLeaves uint64, row, forestRows uint8) bool {
	if treeRows(numLeaves) != forestRows {
		translated := translatePos(position, forestRows, treeRows(numLeaves))
		return isRootPositionOnRow(translated, numLeaves, row)
	}

	return isRootPositionOnRow(position, numLeaves, row)
}

// rootExistsOnRow returns whether or not a root exists on the row with the given num leaves.
func rootExistsOnRow(numLeaves uint64, h uint8) bool {
	return (numLeaves>>h)&1 == 1
}

// isAncestor returns true if the higherPos is an ancestor of the lowerPos.
//
// 14
// |---------------\
// 12              13
// |-------\       |-------\
// 08      09      10      11
// |---\   |---\   |---\   |---\
// 00  01  02  03  04  05  06  07
//
// In the above tree, 12 is an ancestor of 00. 13 is not an ancestor of 00.
func isAncestor(higherPos, lowerPos uint64, forestRows uint8) bool {
	if higherPos == lowerPos {
		return false
	}
	lowerRow := detectRow(lowerPos, forestRows)
	higherRow := detectRow(higherPos, forestRows)

	// Prevent underflows by checking that the higherRow is not less
	// than the lowerRow.
	if higherRow < lowerRow {
		return false
	}

	// Return false if we error out or the calculated ancestor doesn't
	// match the higherPos.
	ancestor, err := parentMany(lowerPos, higherRow-lowerRow, forestRows)
	if err != nil || higherPos != ancestor {
		return false
	}

	return true
}

// removeBit removes the nth bit from the val passed in. For example, if the 2nd
// bit is to be removed from 1011 (11 in dec), the returned value is 111 (7 in dec).
func removeBit(val, bit uint64) uint64 {
	mask := uint64((2 << bit) - 1)
	upperMask := math.MaxUint64 ^ mask
	upper := val & upperMask

	mask = (1 << bit) - 1
	lowerMask := ^(math.MaxUint64 ^ mask)
	lower := val & lowerMask

	return (upper >> 1) | lower
}

// addBit insert a bit into the desired place. For example, if place is 2 and
// bit is true, for value of 1001 (9 in decimal), the returned value is 10101
// (21 in decimal).
func addBit(val, place uint64, bit bool) uint64 {
	mask := uint64((1 << place) - 1)
	upperMask := math.MaxUint64 ^ mask
	upper := val & upperMask
	upper <<= 1

	lowerMask := ^(math.MaxUint64 ^ mask)
	lower := val & lowerMask

	if bit {
		return (upper | lower) | (1 << place)
	}
	return (upper | lower)
}

// calcNextPosition calculates where a position should move to if an ancestor of
// delPos gets deleted.
// NOTE: caller must check that delPos is an ancestor of position. Wrong position
// will be returned if delPos is not an ancestor of position.
//
// Ex: pos of 1, delPos of 5.
// In the below tree, when we delete 5 (101), we'll remove the 1st bit of 1 (001)
// and we get 01. Then we prepend bit 1 on 01 and get 101, which is 5, the position
// 1 needs to go to when we delete 5.
//
// row 2: 110
// -      |---------\
// row 1: 100       101
// -      |----\    |----\
// row 0: 000  001  010  011
//
// TODO? we could have a function that supports moving up multiple rows. Not sure
// if it's needed.
func calcNextPosition(position, delPos uint64, forestRows uint8) (uint64, error) {
	delRow := detectRow(delPos, forestRows)
	posRow := detectRow(position, forestRows)

	if delRow < posRow {
		return 0, fmt.Errorf("calcNextPosition fail. delPos of %d is lower than %d",
			delPos, position)
	}

	// This is the lower bits where we'll remove the nth bit.
	lowerBits := removeBit(position, uint64(delRow-posRow))

	// This is the bit to be prepended.
	toRow := posRow + 1
	higherBits := uint64(1<<toRow) << uint64(forestRows-toRow)

	// Put the bits together and return it.
	return higherBits | lowerBits, nil
}

// calcPrevPosition calculates where a position was previously before delPos was deleted.
//
// Ex: pos of 5, delPos of 5.
// In the below tree, we first flip the row bit for pos 5 (101) and get 001. We then add
// a bit of the del row. Since 5 on the right and is on row 1, we add a single 0 bit at
// the 1st bit and get 001.
//
// row 2 - 110
// -       |---------\
// row 1 - 100       101
// -       |----\    |----\
// row 0 - 000  001  010  011
func calcPrevPosition(position, delPos uint64, forestRows uint8) uint64 {
	delRow := detectRow(delPos, forestRows)
	posRow := detectRow(position, forestRows)

	mask := ^(uint64(1<<posRow) << uint64(forestRows-posRow))
	lowerBits := position
	lowerBits &= mask

	bitToAdd := isLeftNiece(delPos)
	if delRow < posRow {
		if isLeftNiece(delPos) {
			bitToAdd = true
		} else {
			bitToAdd = false
		}
	}

	place := uint64(delRow - (posRow - 1))
	lowerBits = addBit(lowerBits, place, bitToAdd)
	return lowerBits
}

// detectRow finds the current row of your node given the position
// and the total forest rows.
func detectRow(position uint64, forestRows uint8) uint8 {
	marker := uint64(1 << forestRows)
	var h uint8
	for h = 0; position&marker != 0; h++ {
		marker >>= 1
	}

	return h
}

// getLowestRoot returns the row of the lowest root given the number of leaves
// and the forestRows.
func getLowestRoot(numLeaves uint64) uint8 {
	forestRows := treeRows(numLeaves)

	row := uint8(0)
	for ; row <= forestRows; row++ {
		rootPresent := numLeaves&(1<<row) != 0
		if rootPresent {
			break
		}
	}
	return row
}

// detectOffset takes a node position and number of leaves in forest, and
// returns the following:
//
// 1. Which subtree a node is in.
// 2. The height from node to its tree top (which is the bitfield length).
// 3. The L/R bitfield to descend to the node.
func detectOffset(position uint64, numLeaves uint64) (uint8, uint8, uint64, error) {
	tRows := int(treeRows(numLeaves))
	// nr = target node row
	nr := detectRow(position, uint8(tRows))

	origPos := position
	// add trees until you would exceed position of node

	// This is a bit of an ugly predicate.  The goal is to detect if we've
	// gone past the node we're looking for by inspecting progressively shorter
	// trees; once we have, the loop is over.

	// The predicate breaks down into 3 main terms:
	// A: pos << nr
	// B: mask
	// C: 1<<tr & numleaves (treeSize)
	// The predicate is then if (A&B >= C)
	// A is position up-shifted by the row of the node we're targeting.
	// B is the "mask" we use in other functions; a bunch of 0s at the MSB side
	// and then a bunch of 1s on the LSB side, such that we can use bitwise AND
	// to discard high bits. Together, A&B is shifting position up by nr bits,
	// and then discarding (zeroing out) the high bits.  This is the same as in
	// childMany. C checks for whether a tree exists at the current tree
	// rows. If there is no tree at th, C is 0. If there is a tree, it will
	// return a power of 2: the base size of that tree.
	// The C term actually is used 3 times here, which is ugly; it's redefined
	// right on the next line.
	// In total, what this loop does is to take a node position, and
	// see if it's in the next largest tree.  If not, then subtract everything
	// covered by that tree from the position, and proceed to the next tree,
	// skipping trees that don't exist.
	var biggerTrees uint8
	for ; (position<<nr)&maxPosition(uint8(tRows)) >=
		maxLeafCount(uint8(tRows))&numLeaves; tRows-- {

		if tRows < 0 {
			return 0, 0, 0, fmt.Errorf("detectOffest error: "+
				"position %d doesn't exist in a forest with %d leaves",
				origPos, numLeaves)
		}
		treeSize := (1 << tRows) & numLeaves
		if treeSize != 0 {
			position -= treeSize
			biggerTrees++
		}
	}

	// Roots point to their children so we actually need to flip the
	// least significant bit.
	position ^= 1

	// We return the opposite of bits, because we always invert them.
	return biggerTrees, uint8(tRows) - nr, ^position, nil
}

// treeRows returns the number of rows given n leaves.
// Example: The below tree will return 2 as the forest will allocate enough for
// 4 leaves.
//
// row 2:
// .      |-------\
// row 1: 04
// .      |---\   |---\
// row 0: 00  01  02
func treeRows(n uint64) uint8 {
	if n == 0 {
		return 0
	}

	return uint8(bits.Len64(n - 1))
}

// numRoots returns the number of roots that exist with the given number of leaves.
func numRoots(numLeaves uint64) uint8 {
	return uint8(bits.OnesCount64(numLeaves))
}

// maxLeafCount returns the maximum amount of leaves an accumulator of the
// given forestRows can have.
func maxLeafCount(forestRows uint8) uint64 {
	return 1 << forestRows
}

// maxPosition returns the biggest position an accumulator can have for the
// given forestRows.
func maxPosition(forestRows uint8) uint64 {
	return uint64(2<<forestRows) - 1
}

// startPositionAtRow returns the smallest position an accumulator can have for the
// requested row for the given numLeaves.
func startPositionAtRow(row, forestRows uint8) uint64 {
	// 2 << forestRows is 2 more than the max poisition
	// to get the correct offset for a given row,
	// subtract (2 << `row complement of forestRows`) from (2 << forestRows)
	offset := (2 << forestRows) - (2 << (forestRows - row))
	return uint64(offset)
}

// maxPossiblePosAtRow returns the biggest position an accumulator can have for the
// given totalRows.
func maxPossiblePosAtRow(row, totalRows uint8) uint64 {
	mask := uint64(2<<totalRows) - 1
	return ((mask << (totalRows - row)) & mask) - 1
}

// maxPositionAtRow returns the biggest position an accumulator can have for the
// requested row for the given numLeaves.
func maxPositionAtRow(row, forestRows uint8, numLeaves uint64) (uint64, error) {
	max, err := parentMany(numLeaves, row, forestRows)
	if err != nil {
		return 0, err
	}

	// We're returning the position not the leaf count so -1 here.
	if max != 0 {
		max -= 1
	}
	return max, nil
}

// translatePos returns what the given position would be in the to total rows.
func translatePos(pos uint64, fromTotalRow, toTotalRow uint8) uint64 {
	row := detectRow(pos, fromTotalRow)
	if row == 0 {
		return pos
	}
	offset := pos - startPositionAtRow(row, fromTotalRow)
	return offset + startPositionAtRow(row, toTotalRow)
}

// translatePositions allocates and returns what the given slice off position would be in
// the to total rows.
func translatePositions(positions []uint64, fromTotalRow, toTotalRow uint8) []uint64 {
	targets := make([]uint64, len(positions))
	for i := range positions {
		targets[i] = translatePos(positions[i], fromTotalRow, toTotalRow)
	}

	return targets
}

// deTwin goes through the list of sorted deletions and finds the parent deletions.
// NOTE The caller MUST sort the dels before passing it into the function.
//
// Ex: If we're deleting 00 and 01 in this tree:
//
// 02
// |--\
// 00 01
//
// Then we're really deleting 02. The dels of [00, 01] would be [02].
func deTwin(dels []uint64, forestRows uint8) []uint64 {
	for i := 0; i < len(dels); i++ {
		// 1: Check that there's at least 2 elements in the slice left.
		// 2: Check if the right sibling of the current element matches
		//    up with the next element in the slice.
		if i+1 < len(dels) && rightSib(dels[i]) == dels[i+1] {
			// Grab the position of the del.
			pos := dels[i]

			// Delete both of the child nodes from the slice.
			dels = append(dels[:i], dels[i+2:]...)

			// Calculate and insert the parent in order.
			dels = insertInOrder(dels, parent(pos, forestRows))

			// Decrement one since the next element we should
			// look at is at the same index because the slice decreased
			// in length by one.
			i--
		}
	}

	return dels
}

func insertInOrder(dels []uint64, el uint64) []uint64 {
	index := sort.Search(len(dels), func(i int) bool { return dels[i] > el })
	dels = append(dels, 0)
	copy(dels[index+1:], dels[index:])
	dels[index] = el

	return dels
}

// inForest states whether or not a position can exist within the given num leaves and rows.
func inForest(pos, numLeaves uint64, forestRows uint8) bool {
	if pos < numLeaves {
		return true
	}
	marker := uint64(1 << forestRows)
	mask := (marker << 1) - 1
	if pos >= mask {
		return false
	}
	for pos&marker != 0 {
		pos = ((pos << 1) & mask) | 1
	}
	return pos < numLeaves
}

// proofPositions returns all the positions that are needed to prove targets passed in.
// NOTE: the passed in targets MUST be sorted.
func proofPositions(targets []uint64, numLeaves uint64, totalRows uint8) ([]uint64, []uint64) {
	nextTargets := make([]uint64, 0, len(targets))
	nextTargetsIdx := 0

	proofPositions := make([]uint64, 0, len(targets))

	targetsIdx := 0
	for row := uint8(0); row <= totalRows; {
		target, idx, sibIdx := getNextPos(targets, nextTargets, targetsIdx, nextTargetsIdx)
		if idx == -1 {
			// Break if we don't have anymore elements left.
			break
		}
		if idx == 0 {
			targetsIdx++
		} else {
			nextTargetsIdx++
		}

		// Keep incrementing the row if the current position is greater
		// than the max position on this row.
		for target > maxPossiblePosAtRow(row, totalRows) && row <= totalRows {
			row++
		}
		if row > totalRows {
			break
		}

		if isRootPositionOnRowTotalRows(target, numLeaves, row, totalRows) {
			continue
		}

		sibPresent := sibIdx != -1
		if sibPresent {
			if sibIdx == 0 {
				targetsIdx++
			} else if sibIdx == 1 {
				nextTargetsIdx++
			}
		} else {
			proofPositions = append(proofPositions, sibling(target))
		}

		nextTargets = append(nextTargets, parent(target, totalRows))
	}

	return proofPositions, nextTargets
}

// ToString is an interface that different Utreexo implementations have to meet inorder for
// it to use the string functionality.
type ToString interface {
	GetRoots() []Hash
	GetNumLeaves() uint64
	GetHash(uint64) Hash
}

// String prints out the whole thing. Only viable for forest that have height of 5 and less.
func String(ts ToString) string {
	fh := treeRows(ts.GetNumLeaves())

	// The accumulator should be less than 6 rows.
	if fh > 6 {
		s := fmt.Sprintf("Can't print %d leaves. roots:\n", ts.GetNumLeaves())
		roots := ts.GetRoots()
		for i, r := range roots {
			s += fmt.Sprintf("\t%d %x\n", i, r.mini())
		}
		return s
	}

	output := make([]string, (fh*2)+1)
	var pos uint8
	for h := uint8(0); h <= fh; h++ {
		rowlen := uint8(1 << (fh - h))

		for j := uint8(0); j < rowlen; j++ {
			var valstring string
			max, err := maxPositionAtRow(h, fh, ts.GetNumLeaves())
			ok := max >= uint64(pos)
			if ok && err == nil {
				val := ts.GetHash(uint64(pos))
				if val != empty {
					valstring = fmt.Sprintf("%x", val[:2])

					if pos >= 100 {
						valstring = fmt.Sprintf("%x", val[:2])
						valstring = valstring[:len(valstring)-1]
					} else {
						valstring = fmt.Sprintf("%x", val[:2])
					}
				}
			}
			if valstring != "" {
				output[h*2] += fmt.Sprintf("%02d:%s ", pos, valstring)
			} else {
				output[h*2] += "        "
			}
			if h > 0 {
				output[(h*2)-1] += "|-------"
				for q := uint8(0); q < ((1<<h)-1)/2; q++ {
					output[(h*2)-1] += "--------"
				}
				output[(h*2)-1] += "\\       "
				for q := uint8(0); q < ((1<<h)-1)/2; q++ {
					output[(h*2)-1] += "        "
				}

				for q := uint8(0); q < (1<<h)-1; q++ {
					output[h*2] += "        "
				}

			}
			pos++
		}

	}
	var s string
	for z := len(output) - 1; z >= 0; z-- {
		s += output[z] + "\n"
	}
	return s

}

// getRootPosition returns the root of the subtree that this position is included in.
func getRootPosition(position uint64, numLeaves uint64, forestRows uint8) (uint64, error) {
	returnPos := position

	// Since we'll be comparing against the parent of the given position,
	// start one row above.
	h := detectRow(position, forestRows)

	for ; h <= forestRows; h++ {
		rootPos := rootPosition(numLeaves, h, forestRows)
		if rootPos == returnPos {
			return returnPos, nil
		}

		// Grab the parent.
		returnPos = parent(returnPos, forestRows)
	}

	if position != 0 && forestRows != 0 {
		return 0, fmt.Errorf("Couldn't fetch root position. "+
			"Passed in position %d, numLeaves %d, forestRows %d",
			position, numLeaves, forestRows)
	}

	return 0, nil
}

// AllSubTreesToString returns a string of all the individual subtrees in the accumulator.
func AllSubTreesToString(ts ToString) string {
	str := ""
	totalRows := treeRows(ts.GetNumLeaves())
	for h := uint8(0); h < totalRows; h++ {
		rootPos := rootPosition(ts.GetNumLeaves(), h, totalRows)
		if isRootPosition(rootPos, ts.GetNumLeaves()) {
			str += fmt.Sprintf(SubTreeToString(ts, rootPos, false))
			str += "\n"
		}
	}

	return str
}

// SubTreeToString returns a string of the subtree that the position is in.
func SubTreeToString(ts ToString, position uint64, inHex bool) string {
	rootPosition, err := getRootPosition(position, ts.GetNumLeaves(), treeRows(ts.GetNumLeaves()))
	if err != nil {
		return fmt.Sprintf("SubTreeToString error: %v", err.Error())
	}
	subTreeRow := detectRow(rootPosition, treeRows(ts.GetNumLeaves()))

	if subTreeRow > 7 {
		s := fmt.Sprintf("Can't print subtree with rows %d. roots:\n", subTreeRow)
		roots := ts.GetRoots()
		for i, root := range roots {
			miniRoot := root.mini()
			s += fmt.Sprintf("%d %s\n", i, hex.EncodeToString(miniRoot[:]))
		}
		return s
	}

	positionsToRead := []uint64{rootPosition}

	baseLen := 8
	baseSpaceLen := 7

	output := make([]string, (subTreeRow*2)+1)
	for h := int(subTreeRow); h >= 0; h-- {
		nextPositions := []uint64{}

		for _, position := range positionsToRead {
			var readHashString string
			readHash := ts.GetHash(position)

			if readHash != empty {
				if inHex {
					if position > 65535 {
						readHashString = fmt.Sprintf("%x", readHash[:2])
						readHashString = readHashString[:len(readHashString)-3]
					} else if position > 4095 {
						readHashString = fmt.Sprintf("%x", readHash[:2])
						readHashString = readHashString[:len(readHashString)-2]
					} else if position > 255 {
						readHashString = fmt.Sprintf("%x", readHash[:2])
						readHashString = readHashString[:len(readHashString)-1]
					} else {
						readHashString = fmt.Sprintf("%x", readHash[:2])
					}
				} else {
					if position >= 10000 {
						readHashString = fmt.Sprintf("%x", readHash[:2])
						readHashString = readHashString[:len(readHashString)-3]
					} else if position >= 1000 {
						readHashString = fmt.Sprintf("%x", readHash[:2])
						readHashString = readHashString[:len(readHashString)-2]
					} else if position >= 100 {
						readHashString = fmt.Sprintf("%x", readHash[:2])
						readHashString = readHashString[:len(readHashString)-1]
					} else {
						readHashString = fmt.Sprintf("%x", readHash[:2])
					}
				}
			}

			leftChild := leftChild(position, treeRows(ts.GetNumLeaves()))
			rightChild := rightSib(leftChild)
			nextPositions = append(nextPositions, leftChild)
			nextPositions = append(nextPositions, rightChild)

			if readHashString != "" {
				if inHex {
					output[h*2] += fmt.Sprintf("%02x:%s ", position, readHashString)
				} else {
					output[h*2] += fmt.Sprintf("%02d:%s ", position, readHashString)
				}
				// Add spaces.
				totalSpaceLen := baseLen
				for x := 0; x < h; x++ {
					totalSpaceLen *= 2
				}
				totalSpaceLen -= baseSpaceLen
				for j := 1; j < totalSpaceLen; j++ {
					output[h*2] += " "
				}
			} else {
				output[h*2] += "        "

				// Add spaces.
				totalSpaceLen := baseLen
				for x := 0; x < h; x++ {
					totalSpaceLen *= 2
				}
				totalSpaceLen -= baseSpaceLen
				for j := 1; j < totalSpaceLen; j++ {
					output[h*2] += " "
				}
			}

			// Add connections.
			if h > 0 {
				totalLen := baseLen
				for x := 0; x < h-1; x++ {
					totalLen *= 2
				}

				for j := 1; j < totalLen; j++ {
					if j == 1 {
						output[(h*2)-1] += "|"
					}
					output[(h*2)-1] += "-"
				}
				output[(h*2)-1] += "\\"

				for j := 0; j < totalLen-1; j++ {
					output[(h*2)-1] += " "
				}
			}
		}

		positionsToRead = nextPositions
	}

	var s string
	for z := len(output) - 1; z >= 0; z-- {
		s += output[z] + "\n"
	}

	return s
}

// printLeaves returns the leaves encoded to string.
func printLeaves(leaves []Leaf) string {
	str := ""
	for i, leaf := range leaves {
		str += " " + fmt.Sprintf("%s:%v",
			hex.EncodeToString(leaf.Hash[:]), leaf.Remember)

		if i != len(leaves)-1 {
			str += "\n"
		}
	}

	return str
}

// printHashes returns the hashes encoded to string.
func printHashes(hashes []Hash) string {
	str := ""
	for i, hash := range hashes {
		str += " " + hex.EncodeToString(hash[:])

		if i != len(hashes)-1 {
			str += "\n"
		}
	}

	return str
}

// printPolNodes returns the hashes encoded to string of the polNodes passed in.
func printPolNodes(nodes []*polNode) string {
	str := ""
	for i, node := range nodes {
		str += node.String()

		if i != len(nodes)-1 {
			str += "\n"
		}
	}

	return str
}

// nodeMapToString returns all the entries in the node map as a string.
func nodeMapToString(m map[miniHash]*polNode) string {
	str := ""
	idx := 0
	for h, node := range m {
		keyStr := fmt.Sprintf("key:%s, node:%s",
			hex.EncodeToString(h[:]), node.String())

		if idx != 0 {
			str += "\n" + keyStr
		} else {
			str += keyStr
		}
		idx++
	}

	return str
}

// polNodeAndPosToString turns a slice of polNode and pos into readable string.
func polNodeAndPosToString(nodes []nodeAndPos) string {
	str := ""
	for i, node := range nodes {
		str += fmt.Sprintf("pos:%d, node:%s", node.pos, node.node.String())

		if i != len(nodes)-1 {
			str += "\n"
		}
	}

	return str
}

// uint64Cmp compares two uint64 values.
func uint64Cmp(a, b uint64) int {
	if a < b {
		return -1
	} else if a > b {
		return 1
	}
	return 0
}

// intLess is a helper function that is useful for using sorting.
func intLess(a, b int) bool {
	return a < b
}

// uint64Less is a helper function that is useful for using sorting.
func uint64Less(a, b uint64) bool {
	return a < b
}

// copySortedFunc returns a copy of the slice passed in that's sorted.
func copySortedFunc[E any](slice []E, less func(a, b E) bool) []E {
	sliceCopy := make([]E, len(slice))
	copy(sliceCopy, slice)

	slices.SortFunc(sliceCopy, less)
	return sliceCopy
}
