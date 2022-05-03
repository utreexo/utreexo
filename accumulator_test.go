package utreexo

import (
	"encoding/hex"
	"fmt"
	"math/rand"
	"reflect"
	"testing"
)

func (p *Pollard) posMapSanity() error {
	for _, node := range p.nodeMap {
		pos := p.calculatePosition(node)
		gotNode, _, _, err := p.getNode(pos)
		if err != nil {
			return err
		}

		if gotNode == nil {
			return fmt.Errorf("Couldn't fetch pos %d, expected %s",
				pos, hex.EncodeToString(node.data[:]))
		}

		if gotNode.data != node.data {
			return fmt.Errorf("Calculated pos %d for node %s but read %s",
				pos, hex.EncodeToString(node.data[:]),
				hex.EncodeToString(gotNode.data[:]))
		}
	}

	return nil
}

func TestPollardAdditions(t *testing.T) {
	t.Parallel()

	// simulate blocks with simchain
	numAdds := uint32(300)
	sc := newSimChain(0x07)

	p := NewAccumulator(true)
	for b := 0; b < 3000; b++ {
		adds, _, _ := sc.NextBlock(numAdds)

		err := p.Modify(adds, nil, nil)
		if err != nil {
			t.Fatalf("TestSwapLessAddDel fail at block %d. Error: %v", b, err)
		}

		// Check the hashes every 500 blocks.
		if b%500 == 0 {
			for _, root := range p.roots {
				if root.leftNiece != nil && root.rightNiece != nil {
					err = checkHashes(root.leftNiece, root.rightNiece, &p)
					if err != nil {
						t.Fatal(err)
					}
				}
			}
		}

		if uint64(len(p.nodeMap)) != p.numLeaves-p.numDels {
			err := fmt.Errorf("TestSwapLessAdditions fail at block %d: "+
				"have %d leaves in map but only %d leaves in total",
				b, len(p.nodeMap), p.numLeaves-p.numDels)
			t.Fatal(err)
		}
	}
}

func TestPollardAddDel(t *testing.T) {
	t.Parallel()

	// simulate blocks with simchain
	numAdds := uint32(5)
	sc := newSimChain(0x07)

	p := NewAccumulator(true)
	var totalAdds, totalDels int

	for b := 0; b <= 2000; b++ {
		adds, _, delHashes := sc.NextBlock(numAdds)
		totalAdds += len(adds)
		totalDels += len(delHashes)

		proof, err := p.Prove(delHashes)
		if err != nil {
			t.Fatalf("TestSwapLessAddDel fail at block %d. Error: %v", b, err)
		}

		err = p.VerifyAndPopulate(delHashes, proof)
		if err != nil {
			t.Fatal(err)
		}

		for _, target := range proof.Targets {
			n, _, _, err := p.getNode(target)
			if err != nil {
				t.Fatalf("TestSwapLessAddDel fail at block %d. Error: %v", b, err)
			}
			if n == nil {
				t.Fatalf("TestSwapLessAddDel fail to read %d at block %d.", target, b)
			}
		}

		err = p.Modify(adds, delHashes, proof.Targets)
		if err != nil {
			t.Fatalf("TestSwapLessAddDel fail at block %d. Error: %v", b, err)
		}

		if b%100 == 0 {
			for _, root := range p.roots {
				if root.leftNiece != nil && root.rightNiece != nil {
					err = checkHashes(root.leftNiece, root.rightNiece, &p)
					if err != nil {
						t.Fatal(err)
					}
				}
			}
		}

		err = p.posMapSanity()
		if err != nil {
			t.Fatalf("TestSwapLessAddDel fail at block %d. Error: %v",
				b, err)
		}
		if uint64(len(p.nodeMap)) != p.numLeaves-p.numDels {
			err := fmt.Errorf("TestSwapLessAddDel fail at block %d: "+
				"have %d leaves in map but only %d leaves in total",
				b, len(p.nodeMap), p.numLeaves-p.numDels)
			t.Fatal(err)
		}
	}
}

func TestUndo(t *testing.T) {
	t.Parallel()

	var tests = []struct {
		startLeafCount int
		dels           []Hash
		adds           []Leaf
	}{
		{
			8,
			[]Hash{{5}, {6}},
			nil,
		},
		{
			8,
			[]Hash{{4}, {5}},
			nil,
		},
		{
			8,
			nil,
			[]Leaf{{Hash: Hash{9}}, {Hash: Hash{10}}},
		},
		{
			8,
			[]Hash{{4}, {5}},
			[]Leaf{{Hash: Hash{9}}, {Hash: Hash{10}}},
		},
		{
			7,
			[]Hash{{5}, {6}},
			[]Leaf{{Hash: Hash{8}}, {Hash: Hash{9}}},
		},

		{
			12,
			nil,
			[]Leaf{{Hash: Hash{14}}, {Hash: Hash{15}}, {Hash: Hash{16}}, {Hash: Hash{17}}},
		},
	}

	for _, test := range tests {
		p := NewAccumulator(true)

		// Create the starting off pollard.
		adds := make([]Leaf, test.startLeafCount)
		for i := range adds {
			adds[i].Hash[0] = uint8(i + 1)
		}

		err := p.Modify(adds, nil, nil)
		if err != nil {
			t.Fatal(err)
		}

		beforeRoots := p.GetRoots()

		bp, err := p.Prove(test.dels)
		if err != nil {
			t.Fatal(err)
		}

		err = p.Modify(test.adds, test.dels, bp.Targets)
		if err != nil {
			t.Fatal(err)
		}
		for _, root := range p.roots {
			if root.leftNiece != nil && root.rightNiece != nil {
				err = checkHashes(root.leftNiece, root.rightNiece, &p)
				if err != nil {
					t.Fatal(err)
				}
			}
		}

		err = p.Undo(uint64(len(test.adds)), bp.Targets, test.dels)
		if err != nil {
			t.Fatal(err)
		}
		for _, root := range p.roots {
			if root.leftNiece != nil && root.rightNiece != nil {
				err = checkHashes(root.leftNiece, root.rightNiece, &p)
				if err != nil {
					t.Fatal(err)
				}
			}
		}
		if uint64(len(p.nodeMap)) != p.numLeaves-p.numDels {
			err := fmt.Errorf("TestUndo fail have %d leaves in map but only %d leaves in total",
				len(p.nodeMap), p.numLeaves-p.numDels)
			t.Fatal(err)
		}
		err = p.posMapSanity()
		if err != nil {
			err := fmt.Errorf("TestUndo fail: error %v", err)
			t.Fatal(err)
		}

		afterRoots := p.GetRoots()

		if !reflect.DeepEqual(beforeRoots, afterRoots) {
			beforeStr := printHashes(beforeRoots)
			afterStr := printHashes(afterRoots)

			err := fmt.Errorf("PollardUndo Fail: roots don't equal, before %v, after %v",
				beforeStr, afterStr)
			t.Fatal(err)
		}
	}
}

func TestRandUndoAdd(t *testing.T) {
	t.Parallel()

	p := NewAccumulator(true)

	sc := newSimChain(0x07)
	numAdds := uint32(3)
	for b := 0; b <= 1000; b++ {
		adds, durations, delHashes := sc.NextBlock(numAdds)

		beforeRoot := p.GetRoots()
		beforeMap := make(map[miniHash]polNode)
		for key, value := range p.nodeMap {
			beforeMap[key] = *value
		}

		err := p.Modify(adds, nil, nil)
		if err != nil {
			t.Fatalf("TestRandUndoAdd fail at block %d. Error: %v", b, err)
		}

		if b%3 == 2 {
			err := p.Undo(uint64(len(adds)), nil, nil)
			if err != nil {
				t.Fatal(err)
			}

			sc.BackOne(adds, durations, delHashes)
			afterRoot := p.GetRoots()
			if !reflect.DeepEqual(beforeRoot, afterRoot) {
				err := fmt.Errorf("TestRandUndoAdd fail at block %d, "+
					"root mismatch. Before %s, after %s",
					b, printHashes(beforeRoot), printHashes(afterRoot))
				t.Fatal(err)
			}

			if len(p.nodeMap) != len(beforeMap) {
				err := fmt.Errorf("undo map before %d, after %d", len(beforeMap), len(p.nodeMap))
				t.Fatal(err)
			}

			for key, value := range beforeMap {
				node, found := p.nodeMap[key]
				if !found {
					err := fmt.Errorf("hash %s not found after undo",
						hex.EncodeToString(key[:]))
					t.Fatal(err)
				}

				if node.data != value.data {
					err := fmt.Errorf("For hash %s, expected %s, got %s ",
						hex.EncodeToString(key[:]),
						hex.EncodeToString(value.data[:]),
						hex.EncodeToString(node.data[:]))
					t.Fatal(err)
				}
			}
		}

		if b%500 == 0 {
			for _, root := range p.roots {
				if root.leftNiece != nil && root.rightNiece != nil {
					err = checkHashes(root.leftNiece, root.rightNiece, &p)
					if err != nil {
						t.Fatal(err)
					}
				}
			}
		}

		if uint64(len(p.nodeMap)) != p.numLeaves-p.numDels {
			err := fmt.Errorf("TestUndoRand fail at block %d: "+
				"have %d leaves in map but only %d leaves in total",
				b, len(p.nodeMap), p.numLeaves-p.numDels)
			t.Fatal(err)
		}

		err = p.posMapSanity()
		if err != nil {
			err := fmt.Errorf("TestUndoRand fail at block %d: error %v", b, err)
			t.Fatal(err)
		}
	}
}

func TestRandUndo(t *testing.T) {
	t.Parallel()

	p := NewAccumulator(true)

	sc := newSimChain(0x07)
	numAdds := uint32(5)
	for b := 0; b <= 1000; b++ {
		adds, durations, delHashes := sc.NextBlock(numAdds)

		bp, err := p.Prove(delHashes)
		if err != nil {
			t.Fatalf("TestPollardUndoRand fail at block %d. Error: %v", b, err)
		}
		undoTargs := make([]uint64, len(bp.Targets))
		copy(undoTargs, bp.Targets)

		undoDelHashes := make([]Hash, len(delHashes))
		copy(undoDelHashes, delHashes)

		err = p.Verify(delHashes, bp)
		if err != nil {
			t.Fatal(err)
		}

		// We'll be comparing 3 things. Roots, nodeMap and leaf count.
		beforeRoot := p.GetRoots()
		beforeMap := make(map[miniHash]polNode)
		for key, value := range p.nodeMap {
			beforeMap[key] = *value
		}
		beforeLeaves := p.numLeaves

		err = p.Modify(adds, delHashes, bp.Targets)
		if err != nil {
			t.Fatalf("TestRandUndo fail at block %d. Error: %v", b, err)
		}

		if p.numLeaves-uint64(len(adds)) != beforeLeaves {
			err := fmt.Errorf("TestRandUndo fail at block %d. "+
				"Added %d leaves but have %d leaves after modify",
				b, len(adds), p.numLeaves)
			t.Fatal(err)
		}

		// Undo the last modify.
		if b%3 == 0 {
			err := p.Undo(uint64(len(adds)), undoTargs, undoDelHashes)
			if err != nil {
				t.Fatal(err)
			}

			sc.BackOne(adds, durations, delHashes)
			afterRoot := p.GetRoots()
			if !reflect.DeepEqual(beforeRoot, afterRoot) {
				err := fmt.Errorf("TestRandUndo fail at block %d, "+
					"root mismatch. Before %s, after %s",
					b, printHashes(beforeRoot), printHashes(afterRoot))
				t.Fatal(err)
			}

			if len(p.nodeMap) != len(beforeMap) {
				err := fmt.Errorf("TestRandUndo fail at block %d, map length mismatch. "+
					"before %d, after %d", b, len(beforeMap), len(p.nodeMap))
				t.Fatal(err)
			}

			for key, value := range beforeMap {
				node, found := p.nodeMap[key]
				if !found {
					err := fmt.Errorf("TestRandUndo fail at block %d, hash %s not found after undo",
						b, hex.EncodeToString(key[:]))
					t.Fatal(err)
				}

				if node.data != value.data {
					err := fmt.Errorf("TestRandUndo fail at block %d, for hash %s, expected %s, got %s ",
						b, hex.EncodeToString(key[:]),
						hex.EncodeToString(value.data[:]),
						hex.EncodeToString(node.data[:]))
					t.Fatal(err)
				}
			}
		}

		// Check hashes.
		if b%500 == 0 {
			for _, root := range p.roots {
				if root.leftNiece != nil && root.rightNiece != nil {
					err = checkHashes(root.leftNiece, root.rightNiece, &p)
					if err != nil {
						t.Fatal(err)
					}
				}
			}
		}
		if uint64(len(p.nodeMap)) != p.numLeaves-p.numDels {
			err := fmt.Errorf("TestUndoRand fail at block %d: "+
				"have %d leaves in map but only %d leaves in total",
				b, len(p.nodeMap), p.numLeaves-p.numDels)
			t.Fatal(err)
		}

		err = p.posMapSanity()
		if err != nil {
			err := fmt.Errorf("TestUndoRand fail at block %d: error %v", b, err)
			t.Fatal(err)
		}
	}
}

// checkHashes moves down the tree and calculates the parent hash from the children.
// It errors if the calculated hash doesn't match the hash found in the pollard.
func checkHashes(node, sibling *polNode, p *Pollard) error {
	// If node has a niece, then we can calculate the hash of the sibling because
	// every tree is a perfect binary tree.
	if node.leftNiece != nil {
		calculated := parentHash(node.leftNiece.data, node.rightNiece.data)
		if sibling.data != calculated {
			return fmt.Errorf("For position %d, calculated %s from left %s, right %s but read %s",
				p.calculatePosition(sibling),
				hex.EncodeToString(calculated[:]),
				hex.EncodeToString(node.leftNiece.data[:]), hex.EncodeToString(node.rightNiece.data[:]),
				hex.EncodeToString(sibling.data[:]))
		}

		err := checkHashes(node.leftNiece, node.rightNiece, p)
		if err != nil {
			return err
		}
	}

	if sibling.leftNiece != nil {
		calculated := parentHash(sibling.leftNiece.data, sibling.rightNiece.data)
		if node.data != calculated {
			return fmt.Errorf("For position %d, calculated %s from left %s, right %s but read %s",
				p.calculatePosition(node),
				hex.EncodeToString(calculated[:]),
				hex.EncodeToString(sibling.leftNiece.data[:]), hex.EncodeToString(sibling.rightNiece.data[:]),
				hex.EncodeToString(node.data[:]))
		}

		err := checkHashes(sibling.leftNiece, sibling.rightNiece, p)
		if err != nil {
			return err
		}
	}

	return nil
}

// simChain is for testing; it spits out "blocks" of adds and deletes
type simChain struct {
	ttlSlices    [][]Hash
	blockHeight  int32
	leafCounter  uint64
	durationMask uint32
	lookahead    int32
	rnd          *rand.Rand
}

// newSimChain initializes and returns a simchain
func newSimChain(duration uint32) *simChain {
	var s simChain
	s.blockHeight = -1
	s.durationMask = duration
	s.ttlSlices = make([][]Hash, s.durationMask+1)
	s.rnd = rand.New(rand.NewSource(0))
	return &s
}

// newSimChainWithSeed initializes and returns a simchain, with an externally supplied seed
func newSimChainWithSeed(duration uint32, seed int64) *simChain {
	var s simChain
	s.blockHeight = -1
	s.durationMask = duration
	s.ttlSlices = make([][]Hash, s.durationMask+1)
	s.rnd = rand.New(rand.NewSource(seed))
	return &s
}

// BackOne takes the output of NextBlock and undoes the block
func (s *simChain) BackOne(leaves []Leaf, durations []int32, dels []Hash) {

	// push in the deleted hashes on the left, trim the rightmost
	s.ttlSlices = append([][]Hash{dels}, s.ttlSlices[:len(s.ttlSlices)-1]...)

	// Gotta go through the leaves and delete them all from the ttlslices
	for i := range leaves {
		if durations[i] == 0 {
			continue
		}
		s.ttlSlices[durations[i]] =
			s.ttlSlices[durations[i]][:len(s.ttlSlices[durations[i]])-1]
	}

	s.blockHeight--
}

// NextBlock outputs a new simulation block given the additions for the block
// to be outputed
func (s *simChain) NextBlock(numAdds uint32) ([]Leaf, []int32, []Hash) {
	s.blockHeight++

	if s.blockHeight == 0 && numAdds == 0 {
		numAdds = 1
	}
	// they're all forgettable
	adds := make([]Leaf, numAdds)
	durations := make([]int32, numAdds)

	// make dels; dels are preset by the ttlMap
	delHashes := s.ttlSlices[0]
	s.ttlSlices = append(s.ttlSlices[1:], []Hash{})

	// make a bunch of unique adds & make an expiry time and add em to
	// the TTL map
	for j := range adds {
		adds[j].Hash[0] = uint8(s.leafCounter)
		adds[j].Hash[1] = uint8(s.leafCounter >> 8)
		adds[j].Hash[2] = uint8(s.leafCounter >> 16)
		adds[j].Hash[3] = 0xff
		adds[j].Hash[4] = uint8(s.leafCounter >> 24)
		adds[j].Hash[5] = uint8(s.leafCounter >> 32)

		durations[j] = int32(s.rnd.Uint32() & s.durationMask)

		// with "+1", the duration is 1 to 256, so the forest never gets
		// big or tall.  Without the +1, the duration is sometimes 0,
		// which makes a leaf last forever, and the forest will expand
		// over time.

		// the first utxo added lives forever.
		// (prevents leaves from going to 0 which is buggy)
		if s.blockHeight == 0 {
			durations[j] = 0
		}

		if durations[j] != 0 && durations[j] < s.lookahead {
			adds[j].Remember = true
		}

		if durations[j] != 0 {
			s.ttlSlices[durations[j]-1] =
				append(s.ttlSlices[durations[j]-1], adds[j].Hash)
		}

		s.leafCounter++
	}

	return adds, durations, delHashes
}
