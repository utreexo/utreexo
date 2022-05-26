package utreexo

import (
	"crypto/sha512"
	"encoding/hex"
	"fmt"
	"math"
	"math/bits"
	"sort"
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

// isRootPosition checks if the current position is a root given the number of
// leaves and the enitre rows of the forest.
func isRootPosition(position, numLeaves uint64, forestRows uint8) bool {
	row := detectRow(position, forestRows)

	rootPresent := numLeaves&(1<<row) != 0
	rootPos := rootPosition(numLeaves, row, forestRows)

	return rootPresent && rootPos == position
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

// calcNextPosition calculates where a position should move to if an ancestor of
// delPos gets deleted.
// NOTE: caller must check that delPos is an ancestor of position. Wrong position
// will be returned if delPos is not an ancestor of position.
//
// Ex: pos of 1, delPos of 5.
// In the below tree, when we delete 5 (101), we'll remove the 1st bit of 1 (001)
// and we get 01. Then we prepend bit 1 on 01 and get 101, which is 4, the position
// 1 needs to go to when we delete 5.
//
// row 2: 110
//        |---------\
// row 1: 100       101
//        |----\    |----\
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
//        |-------\
// row 1: 04
//        |---\   |---\
// row 0: 00  01  02
func treeRows(n uint64) uint8 {
	// treeRows works by:
	// 1. Find the next power of 2 from the given n leaves.
	// 2. Calculate the log2 of the result from step 1.
	//
	// For example, if the given number is 9, the next power of 2 is
	// 16. This log2 of this number is how many rows there are in the
	// given tree.
	//
	// This works because while Utreexo is a collection of perfect
	// trees, the allocated number of leaves is always a power of 2.
	// For Utreexo trees that don't have leaves that are power of 2,
	// the extra space is just unallocated/filled with zeros.

	// Find the next power of 2
	n--
	n |= n >> 1
	n |= n >> 2
	n |= n >> 4
	n |= n >> 8
	n |= n >> 16
	n |= n >> 32
	n++

	// log of 2 is the tree depth/height
	// if n == 0, there will be 64 traling zeros but actually no tree rows.
	// we clear the 6th bit to return 0 in that case.
	return uint8(bits.TrailingZeros64(n) & ^int(64))

}

// logicalTreeRows returns the number of
//
// Example: The below tree will return 1 as the logical number of rows is 1 for this
// forest.
//
// row 2:
//        |-------\
// row 1: 04
//        |---\   |---\
// row 0: 00  01  02
func logicalTreeRows(n uint64) uint8 {
	return uint8(bits.Len64(n) - 1)
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

// rowLength returns how many elements exist within a given row.
// Example: below forest has 1 element at row 1 and 3 elements at row 0.
//
// row 2:
//        |-------\
// row 1: 04
//        |---\   |---\
// row 0: 00  01  02
func rowLength(row, forestRows uint8) uint8 {
	return uint8(1 << (forestRows - row))
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

// extractRow extracts and returns the targets at the requested row.
func extractRow(targets []uint64, forestRows, rowToExtract uint8) []uint64 {
	if len(targets) < 0 {
		return []uint64{}
	}

	start := -1
	end := 0

	for i := 0; i < len(targets); i++ {
		if detectRow(targets[i], forestRows) == rowToExtract {
			if start == -1 {
				start = i
			}

			end = i
		} else {
			// If we're not at the desired row and start has already been set
			// once, that means we've extracted everything we can. This is
			// possible because the assumption is that the targets are sorted.
			if start != -1 {
				break
			}
		}
	}

	if start == -1 {
		return []uint64{}
	}

	count := (end + 1) - start
	row := make([]uint64, count)

	copy(row, targets[start:end+1])

	return row
}

// proofPositions returns all the positions that are needed to prove targets passed in.
func proofPositions(targets []uint64, numLeaves uint64, forestRows uint8) []uint64 {
	var nextTargets, proofPositions []uint64

	for row := uint8(0); row < forestRows; row++ {
		rowTargs := extractRow(targets, forestRows, row)

		rowTargs = append(rowTargs, nextTargets...)
		sort.Slice(rowTargs, func(a, b int) bool { return rowTargs[a] < rowTargs[b] })

		// Reset nextTargets
		nextTargets = nextTargets[:0]

		if numLeaves&(1<<row) > 0 && len(rowTargs) > 0 &&
			rowTargs[len(rowTargs)-1] == rootPosition(numLeaves, row, forestRows) {
			// remove roots from rowTargs
			rowTargs = rowTargs[:len(rowTargs)-1]
		}

		for len(rowTargs) > 0 {
			switch {
			// look at the first 4 targets
			case len(rowTargs) > 3:
				if (rowTargs[0]|1)^2 == rowTargs[3]|1 {
					// the first and fourth target are cousins
					// => target 2 and 3 are also rowTargs, both parents are
					// rowTargs of next row
					nextTargets = append(nextTargets,
						parent(rowTargs[0], forestRows), parent(rowTargs[3], forestRows))
					rowTargs = rowTargs[4:]
					break
				}
				// handle first three rowTargs
				fallthrough

			// look at the first 3 rowTargs
			case len(rowTargs) > 2:
				if (rowTargs[0]|1)^2 == rowTargs[2]|1 {
					// the first and third target are cousins
					// => the second target is either the sibling of the first
					// OR the sibiling of the third
					// => only the sibling that is not a target is appended
					// to the proof positions
					if rowTargs[1]|1 == rowTargs[0]|1 {
						proofPositions = append(proofPositions, rowTargs[2]^1)
					} else {
						proofPositions = append(proofPositions, rowTargs[0]^1)
					}
					// both parents are rowTargs of next row
					nextTargets = append(nextTargets,
						parent(rowTargs[0], forestRows), parent(rowTargs[2], forestRows))
					rowTargs = rowTargs[3:]
					break
				}
				// handle first two rowTargs
				fallthrough

			// look at the first 2 rowTargs
			case len(rowTargs) > 1:
				if rowTargs[0]|1 == rowTargs[1] {
					nextTargets = append(nextTargets, parent(rowTargs[0], forestRows))
					rowTargs = rowTargs[2:]
					break
				}
				if (rowTargs[0]|1)^2 == rowTargs[1]|1 {
					proofPositions = append(proofPositions, rowTargs[0]^1, rowTargs[1]^1)
					nextTargets = append(nextTargets,
						parent(rowTargs[0], forestRows), parent(rowTargs[1], forestRows))
					rowTargs = rowTargs[2:]
					break
				}
				// not related, handle first target
				fallthrough

			// look at the first target
			default:
				proofPositions = append(proofPositions, rowTargs[0]^1)
				nextTargets = append(nextTargets, parent(rowTargs[0], forestRows))
				rowTargs = rowTargs[1:]
			}
		}
	}

	return proofPositions
}

// String prints out the whole thing. Only viable for forest that have height of 5 and less.
func (p *Pollard) String() string {
	fh := treeRows(p.numLeaves)

	// The accumulator should be less than 6 rows.
	if fh > 6 {
		s := fmt.Sprintf("Can't print %d leaves. roots:\n", p.numLeaves)
		roots := p.GetRoots()
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
			max, err := maxPositionAtRow(h, fh, p.numLeaves)
			ok := max >= uint64(pos)
			if ok && err == nil {
				val := p.getHash(uint64(pos))
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
func (p *Pollard) AllSubTreesToString() string {
	str := ""
	totalRows := treeRows(p.numLeaves)
	for h := uint8(0); h < totalRows; h++ {
		rootPos := rootPosition(p.numLeaves, h, totalRows)
		if isRootPosition(rootPos, p.numLeaves, totalRows) {
			str += fmt.Sprintf(p.SubTreeToString(rootPos, false))
			str += "\n"
		}
	}

	return str
}

// SubTreeToString returns a string of the subtree that the position is in.
func (p *Pollard) SubTreeToString(position uint64, inHex bool) string {
	rootPosition, err := getRootPosition(position, p.numLeaves, treeRows(p.numLeaves))
	if err != nil {
		return fmt.Sprintf("SubTreeToString error: %v", err.Error())
	}
	subTreeRow := detectRow(rootPosition, treeRows(p.numLeaves))

	if subTreeRow > 7 {
		s := fmt.Sprintf("Can't print subtree with rows %d. roots:\n", subTreeRow)
		roots := p.GetRoots()
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
			readHash := p.getHash(position)

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

			leftChild := leftChild(position, treeRows(p.numLeaves))
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
