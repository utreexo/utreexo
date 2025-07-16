package utreexo

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"math/rand"
	"reflect"
	"testing"
)

// Assert that Pollard implements the UtreexoTest interface.
var _ UtreexoTest = (*Pollard)(nil)

// cachedMapToString returns "n/a" as it's not present in Pollard
//
// Implements the UtreexoTest interface.
func (p *Pollard) cachedMapToString() string {
	return "n/a"
}

// nodeMapToString returns the node map as a string.
//
// Implements the UtreexoTest interface.
func (p *Pollard) nodeMapToString() string {
	return nodeMapToString(p.NodeMap)
}

// rootToString returns the roots as a string.
//
// Implements the UtreexoTest interface.
func (p *Pollard) rootToString() string {
	return printHashes(p.GetRoots())
}

// sanityCheck checks that the the node map is refering to a node that has the same position
// and that the leaves hash up to the saved roots.
//
// Implements the UtreexoTest interface.
func (p *Pollard) sanityCheck() error {
	err := p.posMapSanity()
	if err != nil {
		return err
	}

	return p.checkHashes()
}

func (p *Pollard) posMapSanity() error {
	if uint64(len(p.NodeMap)) != p.NumLeaves-p.NumDels {
		err := fmt.Errorf("Have %d leaves in map but only %d leaves in total",
			len(p.NodeMap), p.NumLeaves-p.NumDels)
		return err
	}

	for mHash, node := range p.NodeMap {
		if node == nil {
			return fmt.Errorf("Node in nodemap is nil. Key: %s",
				hex.EncodeToString(mHash[:]))
		}

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

func testUndo(t *testing.T, utreexo UtreexoTest) {
	var tests = []struct {
		startAdds []Hash
		startDels []Hash

		modifyAdds []Hash
		modifyDels []Hash
	}{
		{
			[]Hash{{1}, {2}, {3}, {4}, {5}, {6}},
			nil,

			[]Hash{{7}, {8}},
			[]Hash{{6}, {4}, {2}, {1}, {3}},
		},
		{
			[]Hash{{1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}},
			nil,

			nil,
			[]Hash{{5}, {6}},
		},
		{
			[]Hash{{1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}},
			nil,

			nil,
			[]Hash{{4}, {5}},
		},
		{
			[]Hash{{1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}},
			nil,

			[]Hash{{9}, {10}},
			nil,
		},
		{
			[]Hash{{1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}},
			nil,

			[]Hash{{9}, {10}},
			[]Hash{{4}, {5}},
		},
		{
			[]Hash{{1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}},
			nil,

			[]Hash{{9}, {10}},
			[]Hash{{2}, {3}, {7}},
		},
		{
			[]Hash{{1}, {2}, {3}, {4}, {5}, {6}, {7}},
			nil,

			[]Hash{{8}, {9}},
			[]Hash{{5}, {6}},
		},

		{
			[]Hash{{1}, {2}, {3}, {4}, {5}, {6}, {7}},
			nil,

			[]Hash{{14}, {15}, {16}, {17}},
			nil,
		},

		{
			[]Hash{{1}, {2}, {3}, {4}, {5}, {6}, {7}},
			[]Hash{{1}, {2}, {3}, {4}, {5}, {6}},

			[]Hash{{8}},
			nil,
		},

		{
			[]Hash{{1}, {2}, {3}, {4}, {5}, {6}, {7}},
			[]Hash{{1}, {2}, {3}, {4}, {6}, {7}},

			[]Hash{{8}},
			nil,
		},
	}

	for i, test := range tests {
		switch utreexo.(type) {
		case *Pollard:
			v := NewAccumulator()
			utreexo = &v
		case *MapPollard:
			v := NewMapPollard(false)
			utreexo = &v
		}
		adds := make([]Leaf, len(test.startAdds))
		for i := range adds {
			hash := test.startAdds[i]
			adds[i] = Leaf{Hash: hash, Remember: true}
		}

		// Create the initial starting off pollard.
		err := utreexo.Modify(adds, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}
		proof, err := utreexo.Prove(test.startDels)
		if err != nil {
			t.Fatalf("TestUndo failed %d: error %v", i, err)
		}
		err = utreexo.Modify(nil, test.startDels, proof)
		if err != nil {
			t.Fatalf("TestUndo failed %d: error %v", i, err)
		}

		beforeRoots := utreexo.GetRoots()
		beforeStr := utreexo.String()

		modifyAdds := make([]Leaf, len(test.modifyAdds))
		for i := range modifyAdds {
			hash := test.modifyAdds[i]
			modifyAdds[i] = Leaf{Hash: hash}
		}

		modifyProof, err := utreexo.Prove(test.modifyDels)
		if err != nil {
			t.Fatalf("TestUndo failed %d: error %v", i, err)
		}

		err = proofSanity(modifyProof)
		if err != nil {
			t.Fatalf("TestUndo failed %d: error %v", i, err)
		}

		// Perform the modify to undo.
		err = utreexo.Modify(modifyAdds, test.modifyDels, modifyProof)
		if err != nil {
			t.Fatalf("TestUndo failed %d: error %v", i, err)
		}
		afterStr := utreexo.String()

		err = utreexo.sanityCheck()
		if err != nil {
			str := fmt.Errorf("TestUndo failed %d: error %v"+
				"\nbefore:\n\n%s"+
				"\nafter:\n\n%s",
				i, err,
				beforeStr,
				afterStr)
			t.Fatal(str)
		}

		// Perform the undo.
		err = utreexo.Undo(test.modifyAdds, modifyProof, test.modifyDels, beforeRoots)
		if err != nil {
			err := fmt.Errorf("TestUndo failed %d: error %v"+
				"\nbefore:\n\n%s"+
				"\nafter:\n\n%s",
				i, err,
				beforeStr,
				afterStr)
			t.Fatal(err)
		}
		undoStr := utreexo.String()

		afterRoots := utreexo.GetRoots()
		if !reflect.DeepEqual(beforeRoots, afterRoots) {
			beforeRootsStr := printHashes(beforeRoots)
			afterRootsStr := printHashes(afterRoots)

			err := fmt.Errorf("TestUndo failed %d: roots don't equal."+
				"\nbefore roots:\n%v"+
				"\nafter roots:\n%v"+
				"\nbefore:\n\n%s"+
				"\nafter:\n\n%s"+
				"\nundo:\n\n%s",
				i,
				beforeRootsStr,
				afterRootsStr,
				beforeStr,
				afterStr,
				undoStr)
			t.Fatal(err)
		}

		err = utreexo.sanityCheck()
		if err != nil {
			err := fmt.Errorf("TestUndo fail: error %v"+
				"\nbefore:\n\n%s"+
				"\nafter:\n\n%s"+
				"\nundo:\n\n%s",
				err,
				beforeStr,
				afterStr,
				undoStr)
			t.Fatal(err)
		}
	}
}

func TestUndo(t *testing.T) {
	t.Parallel()

	testUndo(t, &Pollard{})
	testUndo(t, &MapPollard{})
}

// checkHashes moves down the tree and calculates the parent hash from the children.
// It errors if the calculated hash doesn't match the hash found in the pollard.
func checkHashes(node, sibling *polNode, p *Pollard) error {
	// If node has a niece, then we can calculate the hash of the sibling because
	// every tree is a perfect binary tree.
	if node.lNiece != nil {
		calculated := parentHash(node.lNiece.data, node.rNiece.data)
		if sibling.data != calculated {
			return fmt.Errorf("For position %d, calculated %s from left %s, right %s but read %s",
				p.calculatePosition(sibling),
				hex.EncodeToString(calculated[:]),
				hex.EncodeToString(node.lNiece.data[:]), hex.EncodeToString(node.rNiece.data[:]),
				hex.EncodeToString(sibling.data[:]))
		}

		err := checkHashes(node.lNiece, node.rNiece, p)
		if err != nil {
			return err
		}
	}

	if sibling.lNiece != nil {
		calculated := parentHash(sibling.lNiece.data, sibling.rNiece.data)
		if node.data != calculated {
			return fmt.Errorf("For position %d, calculated %s from left %s, right %s but read %s",
				p.calculatePosition(node),
				hex.EncodeToString(calculated[:]),
				hex.EncodeToString(sibling.lNiece.data[:]), hex.EncodeToString(sibling.rNiece.data[:]),
				hex.EncodeToString(node.data[:]))
		}

		err := checkHashes(sibling.lNiece, sibling.rNiece, p)
		if err != nil {
			return err
		}
	}

	return nil
}

// checkHashes is a wrapper around the checkHashes function. Provides an easy function to
// check that the pollard has correct hashes.
func (p *Pollard) checkHashes() error {
	for _, root := range p.Roots {
		if root.lNiece != nil && root.rNiece != nil {
			// First check the root hash.
			calculatedHash := parentHash(root.lNiece.data, root.rNiece.data)
			if calculatedHash != root.data {
				err := fmt.Errorf("For position %d, calculated %s from left %s, right %s but read %s",
					p.calculatePosition(root),
					hex.EncodeToString(calculatedHash[:]),
					hex.EncodeToString(root.lNiece.data[:]), hex.EncodeToString(root.rNiece.data[:]),
					hex.EncodeToString(root.data[:]))
				return err
			}

			// Then check all other hashes.
			err := checkHashes(root.lNiece, root.rNiece, p)
			if err != nil {
				return err
			}
		}
	}

	return nil
}

// positionSanity tries to grab all the eligible positions of the pollard and
// calculates its position. Returns an error if the position calculated does
// not match the position used to fetch the node.
func (p *Pollard) positionSanity() error {
	totalRows := TreeRows(p.NumLeaves)

	for row := uint8(0); row < totalRows; row++ {
		pos := startPositionAtRow(row, totalRows)
		maxPosAtRow, err := maxPositionAtRow(row, totalRows, p.NumLeaves)
		if err != nil {
			return fmt.Errorf("positionSanity fail. Error %v", err)
		}

		for pos < maxPosAtRow {
			node, _, _, err := p.getNode(pos)
			if err != nil {
				return fmt.Errorf("positionSanity fail. Error %v", err)
			}

			if node != nil {
				gotPos := p.calculatePosition(node)

				if gotPos != pos {
					err := fmt.Errorf("expected %d but got %d for. Node: %s",
						pos, gotPos, node.String())
					return fmt.Errorf("positionSanity fail. Error %v", err)
				}
			}

			pos++
		}
	}

	return nil
}

func testModify(t *testing.T, utreexo UtreexoTest) {
	tests := []struct {
		mods []singleModify
	}{
		// Creates a tree like below. em stands for empty (aka zombie) root.
		//
		// |-----------------------------------------------\
		// em
		// |-----------------------\                       |-----------------------\
		//                                                 58
		// |-----------\           |-----------\           |-----------\           |-----------\
		//                                                 52          53          54
		// |-----\     |----\      |-----\     |-----\     |-----\     |-----\     |-----\     |-----\
		//                                                             42    43    44    45    46
		// |--\  |--\  |--\  |--\  |--\  |--\  |--\  |--\  |--\  |--\  |--\  |--\  |--\  |--\  |--\  |--\
		//                                                                               26 27       em
		{
			mods: []singleModify{
				// 1st modify.
				{
					[]Leaf{
						{Hash{1}, true},
						{Hash{2}, true},
						{Hash{3}, true},
						{Hash{4}, true},
						{Hash{5}, true},
						{Hash{6}, true},
						{Hash{7}, true},
						{Hash{8}, true},
						{Hash{9}, true},
						{Hash{10}, true},
						{Hash{11}, true},
						{Hash{12}, true},
						{Hash{13}, true},
						{Hash{14}, true},
						{Hash{15}, true},
						{Hash{16}, true},
						{Hash{17}, true},
						{Hash{18}, true},
						{Hash{19}, true},
						{Hash{20}, true},
						{Hash{21}, true},
						{Hash{22}, false},
						{Hash{23}, false},
						{Hash{24}, false},
						{Hash{25}, true},
						{Hash{26}, false},
						{Hash{27}, false},
						{Hash{28}, false},
						{Hash{29}, true},
						{Hash{30}, false},
						{Hash{31}, true},
					},
					[]Hash{
						// Positions 0-20.
						{1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}, {9}, {10}, {11},
						{12}, {13}, {14}, {15}, {16}, {17}, {18}, {19}, {20}, {21},

						// 24, 28 and 30.
						{25}, {29}, {31},
					},
				},

				// 2nd modify.
				{
					[]Leaf{
						{Hash{32}, false},
					},
					[]Hash{},
				},
			},
		},
	}

	for _, test := range tests {
		for _, mod := range test.mods {
			err := applySingleModify(utreexo, mod.adds, mod.dels)
			if err != nil {
				t.Fatal(err)
			}

			err = utreexo.sanityCheck()
			if err != nil {
				t.Fatal(err)
			}
		}
	}
}

func TestModify(t *testing.T) {
	t.Parallel()

	acc := NewAccumulator()
	testModify(t, &acc)

	mp := NewMapPollard(false)
	testModify(t, &mp)

	mpFull := NewMapPollard(true)
	testModify(t, &mpFull)
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

// getAddsAndDels generates leaves to add and then randomly grabs some of those
// leaves to be deleted.
//
// NOTE if getAddsAndDels are called multiple times for the same pollard, pass in
// p.NumLeaves into getAddsAndDels after the pollard has been modified with the
// previous set of adds and deletions. The leaves genereated are not random and
// are just the next leaf encoded to a 32 byte hash.
func getAddsAndDels(currentLeaves, addCount, delCount uint32) ([]Leaf, []Hash, []uint64) {
	if addCount == 0 {
		return nil, nil, nil
	}
	leaves := make([]Leaf, addCount)
	for i := uint32(0); i < addCount; i++ {
		// Convert int to byte slice.
		bs := make([]byte, 32)
		hashInt := i + currentLeaves
		binary.LittleEndian.PutUint32(bs, hashInt)

		// Add FF at the end as you can't add an empty leaf to the accumulator.
		bs[31] = 0xFF

		// Hash the byte slice.
		leaves[i] = Leaf{Hash: *(*Hash)(bs)}
	}

	delHashes := make([]Hash, delCount)
	delTargets := make([]uint64, delCount)

	prevIdx := make(map[int]struct{})
	for i := range delHashes {
		var idx int
		for {
			if addCount == 1 {
				idx = 0
				prevIdx[idx] = struct{}{}
				break
			} else {
				idx = rand.Intn(int(addCount))
				_, found := prevIdx[idx]
				if !found {
					prevIdx[idx] = struct{}{}
					break
				}
			}
		}

		delHashes[i] = leaves[idx].Hash
		delTargets[i] = uint64(idx)
		leaves[idx].Remember = true
	}

	return leaves, delHashes, delTargets
}

// proofSanity checks that a given proof doesn't have duplicate targets.
func proofSanity(proof Proof) error {
	targetMap := make(map[uint64]int)
	for idx, target := range proof.Targets {
		foundIdx, found := targetMap[target]
		if found {
			return fmt.Errorf("proofSanity fail. Found duplicate target "+
				"at idx %d and %d in targets: %v", foundIdx, idx, proof.Targets)
		}

		targetMap[target] = idx
	}

	return nil
}

func FuzzModify(f *testing.F) {
	var tests = []struct {
		startLeaves uint32
		modifyAdds  uint32
		delCount    uint32
	}{
		{
			8,
			2,
			3,
		},
		{
			6,
			2,
			5,
		},
	}
	for _, test := range tests {
		f.Add(test.startLeaves, test.modifyAdds, test.delCount)
	}

	f.Fuzz(func(t *testing.T, startLeaves uint32, modifyAdds uint32, delCount uint32) {
		t.Parallel()

		p := NewAccumulator()
		fuzzModify(t, &p, startLeaves, modifyAdds, delCount)

		p1 := NewMapPollard(false)
		fuzzModify(t, &p1, startLeaves, modifyAdds, delCount)
	})
}

func fuzzModify(t *testing.T, p UtreexoTest, startLeaves, modifyAdds, delCount uint32) {
	// delCount must be less than the current number of leaves.
	if delCount > startLeaves {
		return
	}

	leaves, delHashes, delTargets := getAddsAndDels(uint32(p.GetNumLeaves()), startLeaves, delCount)
	err := p.Modify(leaves, nil, Proof{})
	if err != nil {
		t.Fatal(err)
	}
	beforeStr := p.String()
	beforeMap := p.nodeMapToString()
	beforeCached := p.cachedMapToString()

	modifyLeaves, _, _ := getAddsAndDels(uint32(p.GetNumLeaves()), modifyAdds, 0)
	err = p.Modify(modifyLeaves, delHashes, Proof{Targets: delTargets})
	if err != nil {
		t.Fatal(err)
	}
	afterStr := p.String()
	afterMap := p.nodeMapToString()
	afterCached := p.cachedMapToString()

	err = p.sanityCheck()
	if err != nil {
		startHashes := make([]Hash, len(leaves))
		for i, leaf := range leaves {
			startHashes[i] = leaf.Hash
		}

		modifyHashes := make([]Hash, len(modifyLeaves))
		for i, leaf := range modifyLeaves {
			modifyHashes[i] = leaf.Hash
		}
		err := fmt.Errorf("FuzzModify fail: %v. "+
			"\nbefore:\n\n%s"+
			"\nafter:\n\n%s"+
			"\nstartLeaves %d, modifyAdds %d, delCount %d, "+
			"\nstartHashes:\n%s"+
			"\nmodifyAdds:\n%s"+
			"\nmodifyDels:\n%s"+
			"\ndel targets:\n %v"+
			"\nnodemap before modify:\n %s"+
			"\nnodemap after modify:\n %s"+
			"\ncachedmap before modify:\n %s"+
			"\ncachedmap after modify:\n %s",
			err,
			beforeStr,
			afterStr,
			startLeaves, modifyAdds, delCount,
			printHashes(startHashes),
			printHashes(modifyHashes),
			printHashes(delHashes),
			delTargets,
			beforeMap,
			afterMap,
			beforeCached,
			afterCached)
		t.Fatal(err)
	}
}

func FuzzModifyChain(f *testing.F) {
	var tests = []struct {
		numAdds  uint32
		duration uint32
		seed     int64
	}{
		{3, 0x07, 0x07},
	}
	for _, test := range tests {
		f.Add(test.numAdds, test.duration, test.seed)
	}

	f.Fuzz(func(t *testing.T, numAdds, duration uint32, seed int64) {
		t.Parallel()

		// simulate blocks with simchain
		sc := newSimChainWithSeed(duration, seed)

		p := NewAccumulator()
		var totalAdds, totalDels int
		for b := 0; b <= 100; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)
			totalAdds += len(adds)
			totalDels += len(delHashes)

			proof, err := p.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzModifyChain fail at block %d. Error: %v", b, err)
			}

			err = p.Verify(delHashes, proof, false)
			if err != nil {
				t.Fatal(err)
			}

			for _, target := range proof.Targets {
				n, _, _, err := p.getNode(target)
				if err != nil {
					t.Fatalf("FuzzModifyChain fail at block %d. Error: %v", b, err)
				}
				if n == nil {
					t.Fatalf("FuzzModifyChain fail to read %d at block %d.", target, b)
				}
			}

			err = p.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("FuzzModifyChain fail at block %d. Error: %v", b, err)
			}

			if b%10 == 0 {
				err = p.checkHashes()
				if err != nil {
					t.Fatal(err)
				}
			}

			err = p.posMapSanity()
			if err != nil {
				t.Fatalf("FuzzModifyChain fail at block %d. Error: %v",
					b, err)
			}
			if uint64(len(p.NodeMap)) != p.NumLeaves-p.NumDels {
				err := fmt.Errorf("FuzzModifyChain fail at block %d: "+
					"have %d leaves in map but only %d leaves in total",
					b, len(p.NodeMap), p.NumLeaves-p.NumDels)
				t.Fatal(err)
			}

			err = p.positionSanity()
			if err != nil {
				t.Fatal(err)
			}
		}
	})
}

func FuzzUndo(f *testing.F) {
	var tests = []struct {
		startLeaves uint8
		modifyAdds  uint8
		delCount    uint8
	}{
		{
			8,
			2,
			3,
		},
		{
			6,
			2,
			5,
		},
	}

	for _, test := range tests {
		f.Add(test.startLeaves, test.modifyAdds, test.delCount)
	}

	f.Fuzz(func(t *testing.T, startLeaves uint8, modifyAdds uint8, delCount uint8) {
		t.Parallel()

		fuzzUndo(t, &Pollard{}, startLeaves, modifyAdds, delCount)
		fuzzUndo(t, &MapPollard{}, startLeaves, modifyAdds, delCount)
	})
}

func fuzzUndo(t *testing.T, p UtreexoTest, startLeaves uint8, modifyAdds uint8, delCount uint8) {
	// delCount must be less than the current number of leaves.
	if delCount > startLeaves {
		return
	}

	// Create the starting off pollard.
	switch p.(type) {
	case *Pollard:
		v := NewAccumulator()
		p = &v
	case *MapPollard:
		v := NewMapPollard(false)
		p = &v
	}
	// Create the starting off pollard.
	leaves, dels, _ := getAddsAndDels(uint32(p.GetNumLeaves()), uint32(startLeaves), uint32(delCount))
	err := p.Modify(leaves, nil, Proof{})
	if err != nil {
		t.Fatal(err)
	}

	beforeStr := p.String()

	beforeRoots := p.GetRoots()
	beforeMap := p.nodeMapToString()

	bp, err := p.Prove(dels)
	if err != nil {
		t.Fatal(err)
	}

	err = proofSanity(bp)
	if err != nil {
		t.Fatal(err)
	}

	if p.GetNumLeaves() != 1 && len(bp.Targets) != len(dels) {
		err := fmt.Errorf("Have %d targets but %d target hashes",
			len(bp.Targets), len(dels))
		t.Fatal(err)
	}

	modifyLeaves, _, _ := getAddsAndDels(uint32(p.GetNumLeaves()), uint32(modifyAdds), 0)
	err = p.Modify(modifyLeaves, dels, bp)
	if err != nil {
		t.Fatal(err)
	}
	afterStr := p.String()
	afterMap := p.nodeMapToString()

	modifyAddHashes := make([]Hash, len(modifyLeaves))
	for i, modifyAdd := range modifyLeaves {
		modifyAddHashes[i] = modifyAdd.Hash
	}
	err = p.Undo(modifyAddHashes, bp, dels, beforeRoots)
	if err != nil {
		startHashes := make([]Hash, len(leaves))
		for i, leaf := range leaves {
			startHashes[i] = leaf.Hash
		}

		modifyHashes := make([]Hash, len(modifyLeaves))
		for i, leaf := range modifyLeaves {
			modifyHashes[i] = leaf.Hash
		}
		err := fmt.Errorf("FuzzUndo fail: Undo failed, error: %v"+
			"\nbefore:\n\n%s"+
			"\nafter:\n\n%s"+
			"\nstartLeaves %d, modifyAdds %d, delCount %d"+
			"\nstartHashes:\n%s"+
			"\nmodifyAdds:\n%s"+
			"\nmodifyDels:\n%s"+
			"\ndel targets:\n %v"+
			"\nnodemap before modify:\n %s"+
			"\nnodemap after modify:\n %s",
			err,
			beforeStr,
			afterStr,
			startLeaves, modifyAdds, delCount,
			printHashes(startHashes),
			printHashes(modifyHashes),
			printHashes(dels),
			bp.Targets,
			beforeMap,
			afterMap)
		t.Fatal(err)
	}
	undoStr := p.String()
	undoMap := p.nodeMapToString()

	// Check that all the parent hashes are correct after the undo.
	err = p.sanityCheck()
	if err != nil {
		startHashes := make([]Hash, len(leaves))
		for i, leaf := range leaves {
			startHashes[i] = leaf.Hash
		}

		modifyHashes := make([]Hash, len(modifyLeaves))
		for i, leaf := range modifyLeaves {
			modifyHashes[i] = leaf.Hash
		}
		retErr := fmt.Errorf("FuzzUndo fail: error: %v "+
			"\nbefore:\n\n%s"+
			"\nafter:\n\n%s"+
			"\nundo:\n\n%s"+
			"\nstartLeaves %d, modifyAdds %d, delCount %d, "+
			"\nstartHashes:\n%s"+
			"\nmodifyAdds:\n%s"+
			"\nmodifyDels:\n%s"+
			"\ndel targets:\n %v"+
			"\nnodemap before modify:\n %s"+
			"\nnodemap after modify:\n %s"+
			"\nnodemap after undo:\n %s",
			err,
			beforeStr,
			afterStr,
			undoStr,
			startLeaves, modifyAdds, delCount,
			printHashes(startHashes),
			printHashes(modifyHashes),
			printHashes(dels),
			bp.Targets,
			beforeMap,
			afterMap,
			undoMap)
		t.Fatal(retErr)
	}

	afterRoots := p.GetRoots()

	if !reflect.DeepEqual(beforeRoots, afterRoots) {
		startHashes := make([]Hash, len(leaves))
		for i, leaf := range leaves {
			startHashes[i] = leaf.Hash
		}

		modifyHashes := make([]Hash, len(modifyLeaves))
		for i, leaf := range modifyLeaves {
			modifyHashes[i] = leaf.Hash
		}

		err := fmt.Errorf("FuzzUndo fail: roots don't equal after the undo. "+
			"\nbefore:\n\n%s"+
			"\nafter:\n\n%s"+
			"\nundo:\n\n%s"+
			"\nstartLeaves %d, modifyAdds %d, delCount %d, "+
			"\nstartHashes:\n%s"+
			"\nmodifyAdds:\n%s"+
			"\nmodifyDels:\n%s"+
			"\ndel targets:\n %v"+
			"\nnodemap before modify:\n %s"+
			"\nnodemap after modify:\n %s"+
			"\nnodemap after undo:\n %s",
			beforeStr,
			afterStr,
			undoStr,
			startLeaves, modifyAdds, delCount,
			printHashes(startHashes),
			printHashes(modifyHashes),
			printHashes(dels),
			bp.Targets,
			beforeMap,
			afterMap,
			undoMap)
		t.Fatal(err)
	}
}

func FuzzUndoChain(f *testing.F) {
	var tests = []struct {
		numAdds  uint32
		duration uint32
		seed     int64
	}{
		{3, 0x07, 0x07},
	}
	for _, test := range tests {
		f.Add(test.numAdds, test.duration, test.seed)
	}

	f.Fuzz(func(t *testing.T, numAdds, duration uint32, seed int64) {
		t.Parallel()

		// We have to do this because the fuzz will give process hung or
		// terminated unexpectedly error.
		if numAdds > 1500 {
			return
		}
		numBlocks := uint32(100)
		if numAdds > 1000 {
			numBlocks = 20
		} else if numAdds > 500 {
			numBlocks = 30
		} else if numAdds > 100 {
			numBlocks = 50
		}

		// Only run either or since if we run both the fuzz test will give process
		// hung or terminated unexpectedly error.
		if numAdds&1 == 1 {
			p := NewAccumulator()
			fuzzUndoChain(t, &p, numBlocks, numAdds, duration, seed)
		} else {
			p1 := NewMapPollard(false)
			fuzzUndoChain(t, &p1, numBlocks, numAdds, duration, seed)
		}
	})
}

func fuzzUndoChain(t *testing.T, p UtreexoTest, blockCount, numAdds, duration uint32, seed int64) {
	full := NewAccumulator()

	undoData := []struct {
		proof     Proof
		hashes    []Hash
		prevRoots []Hash
		adds      []Leaf
		nodeMap   map[miniHash]polNode
	}{}
	// Simulate blocks with simchain.
	sc := newSimChainWithSeed(duration, seed)
	for b := 0; b <= int(blockCount); b++ {
		adds, _, delHashes := sc.NextBlock(numAdds)

		fullProof, err := full.Prove(delHashes)
		if err != nil {
			t.Fatal(err)
		}

		err = full.Modify(adds, delHashes, fullProof)
		if err != nil {
			t.Fatal(err)
		}

		err = p.Verify(delHashes, fullProof, true)
		if err != nil {
			t.Fatal(err)
		}

		bp, err := p.Prove(delHashes)
		if err != nil {
			t.Fatalf("FuzzUndoChain fail at block %d. Error: %v", b, err)
		}

		for i := range bp.Targets {
			var gotHash Hash
			if TreeRows(p.GetNumLeaves()) != p.GetTreeRows() {
				gotHash = p.GetHash(translatePos(bp.Targets[i], TreeRows(p.GetNumLeaves()), p.GetTreeRows()))
			} else {
				gotHash = p.GetHash(bp.Targets[i])
			}

			if gotHash != delHashes[i] {
				t.Fatalf("FuzzUndoChain fail at block %d. For pos %d, expected %s, got %s",
					b, i, delHashes[i], gotHash)
			}
		}

		undoProof := Proof{Targets: make([]uint64, len(bp.Targets)), Proof: make([]Hash, len(bp.Proof))}
		copy(undoProof.Targets, bp.Targets)
		copy(undoProof.Proof, bp.Proof)

		undoDelHashes := make([]Hash, len(delHashes))
		copy(undoDelHashes, delHashes)

		// We'll be comparing 3 things. Roots, nodeMap and leaf count.
		beforeRoot := p.GetRoots()
		if uint8(len(beforeRoot)) != numRoots(p.GetNumLeaves()) {
			t.Fatalf("For %d numleaves, expected %d root but got %d roots:\n%s\n",
				p.GetNumLeaves(), numRoots(p.GetNumLeaves()), len(beforeRoot), printHashes(beforeRoot))
		}
		beforeMap := make(map[miniHash]polNode)

		switch v := p.(type) {
		case *Pollard:
			for key, value := range v.NodeMap {
				beforeMap[key] = *value
			}
		}

		beforeLeaves := p.GetNumLeaves()

		undoData = append(undoData, struct {
			proof     Proof
			hashes    []Hash
			prevRoots []Hash
			adds      []Leaf
			nodeMap   map[miniHash]polNode
		}{
			undoProof,
			undoDelHashes,
			beforeRoot,
			adds,
			beforeMap,
		})

		err = p.Modify(adds, delHashes, bp)
		if err != nil {
			t.Fatalf("FuzzUndoChain fail at block %d. Error: %v", b, err)
		}

		if p.GetNumLeaves()-uint64(len(adds)) != beforeLeaves {
			err := fmt.Errorf("FuzzUndoChain fail at block %d. "+
				"Added %d leaves but have %d leaves after modify",
				b, len(adds), p.GetNumLeaves())
			t.Fatal(err)
		}

		err = p.sanityCheck()
		if err != nil {
			t.Fatal(err)
		}

		// Undo the last 10 modifies and re-do them.
		if b%10 == 9 {
			for i := 9; i >= 0; i-- {
				copyProof := Proof{Targets: make([]uint64, len(undoData[i].proof.Targets)), Proof: make([]Hash, len(undoData[i].proof.Proof))}
				copy(copyProof.Targets, undoData[i].proof.Targets)
				copy(copyProof.Proof, undoData[i].proof.Proof)

				addHashes := make([]Hash, len(undoData[i].adds))
				for j, add := range undoData[i].adds {
					addHashes[j] = add.Hash
				}
				err := p.Undo(addHashes, copyProof, undoData[i].hashes, undoData[i].prevRoots)
				if err != nil {
					t.Fatal(err)
				}

				// Sanity check after the undo.
				err = p.sanityCheck()
				if err != nil {
					t.Fatal(err)
				}

				afterRoot := p.GetRoots()
				if !reflect.DeepEqual(undoData[i].prevRoots, afterRoot) {
					err := fmt.Errorf("FuzzUndoChain fail at block %d, "+
						"root mismatch.\nBefore:\n%s\nAfter:\n%s",
						b-(10-i), printHashes(undoData[i].prevRoots), printHashes(afterRoot))
					t.Fatal(err)
				}

				switch v := p.(type) {
				case *Pollard:
					if len(v.NodeMap) != len(undoData[i].nodeMap) {
						err := fmt.Errorf("FuzzUndoChain fail at block %d, map length mismatch. "+
							"before %d, after %d", b-(10-i), len(undoData[i].nodeMap), len(v.NodeMap))
						t.Fatal(err)
					}

					for key, value := range undoData[i].nodeMap {
						node, found := v.NodeMap[key]
						if !found {
							err := fmt.Errorf("FuzzUndoChain fail at block %d, hash %s not found after undo",
								b-(10-i), hex.EncodeToString(key[:]))
							t.Fatal(err)
						}

						if node.data != value.data {
							err := fmt.Errorf("FuzzUndoChain fail at block %d, for hash %s, expected %s, got %s ",
								b-(10-i), hex.EncodeToString(key[:]),
								hex.EncodeToString(value.data[:]),
								hex.EncodeToString(node.data[:]))
							t.Fatal(err)
						}
					}
				}
			}

			// Undo the undos.
			for i := 0; i < 10; i++ {
				adds, delHashes, bp := undoData[i].adds, undoData[i].hashes, undoData[i].proof

				switch v := p.(type) {
				case *Pollard:
				case *MapPollard:
					v.Ingest(delHashes, bp)
					err = p.sanityCheck()
					if err != nil {
						t.Fatal(err)
					}
				}
				err = p.Modify(adds, delHashes, bp)
				if err != nil {
					t.Fatalf("FuzzUndoChain fail at block %d. Error: %v", b, err)
				}
				err = p.sanityCheck()
				if err != nil {
					t.Fatal(err)
				}
			}

			undoData = undoData[:0]
		}
	}
}

func FuzzWriteAndRead(f *testing.F) {
	var tests = []struct {
		numAdds  uint32
		duration uint32
		seed     int64
	}{
		{3, 0x07, 0x07},
	}
	for _, test := range tests {
		f.Add(test.numAdds, test.duration, test.seed)
	}

	f.Fuzz(func(t *testing.T, numAdds, duration uint32, seed int64) {
		t.Parallel()

		rand.Seed(seed)

		// simulate blocks with simchain
		sc := newSimChainWithSeed(duration, seed)

		p := NewAccumulator()
		var totalAdds, totalDels int
		for b := 0; b <= 100; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)
			totalAdds += len(adds)
			totalDels += len(delHashes)

			proof, err := p.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzWriteAndRead fail at block %d. Error: %v", b, err)
			}

			err = p.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("FuzzWriteAndRead fail at block %d. Error: %v", b, err)
			}
		}
		err := p.checkHashes()
		if err != nil {
			t.Fatal(err)
		}

		// Write to the buffer.
		size := p.SerializeSize()
		buf := bytes.NewBuffer(make([]byte, 0, size))
		wroteBytes, err := p.WriteTo(buf)
		if err != nil {
			t.Fatal(err)
		}

		if wroteBytes != int64(size) {
			t.Fatalf("FuzzWriteAndRead Fail. Wrote %d but serializeSize got %d", wroteBytes, size)
		}

		// Copy and mutate the buffer and attempt to restore from that. Should error out.
		copyBytes := make([]byte, size)
		copy(copyBytes, buf.Bytes())
		copyBytes[0], copyBytes[1] = 0xff, 0xff
		copyBuf := bytes.NewBuffer(copyBytes)
		_, _, err = RestorePollardFrom(copyBuf)
		if err == nil {
			t.Fatalf("FuzzWriteAndRead Fail. Expected an error from reading a corrupted buffer but got nil")
		}

		// Restore from the buffer.
		readBytes, newP, err := RestorePollardFrom(buf)
		if err != nil {
			t.Fatal(err)
		}
		if readBytes != wroteBytes {
			t.Fatalf("FuzzWriteAndRead Fail. Wrote %d but read %d", readBytes, wroteBytes)
		}

		// Check that the node maps are equal.
		err = compareNodeMap(p.NodeMap, newP.NodeMap)
		if err != nil {
			t.Fatal(err)
		}

		err = newP.posMapSanity()
		if err != nil {
			t.Fatal(err)
		}

		err = newP.positionSanity()
		if err != nil {
			t.Fatal(err)
		}

		// Check that the hashes of the roots are correct.
		err = newP.checkHashes()
		if err != nil {
			t.Fatal(err)
		}

		// Compare the roots.
		for i, root := range p.Roots {
			if newP.Roots[i].data != root.data {
				t.Fatalf("FuzzReadAndWrite Fail. Roots don't equal.\nOrig roots:\n%s\nNew roots:\n%s\n",
					printPolNodes(p.Roots), printPolNodes(newP.Roots))
			}
		}
	})
}

// compareNodeMap compares the two maps and returns an error if the two maps do not
// include the same keys and values for those keys.
func compareNodeMap(mapA, mapB map[miniHash]*polNode) error {
	mapAUnique := []*polNode{}
	mapBUnique := []*polNode{}

	mapADiffer := [][]*polNode{}
	mapBDiffer := [][]*polNode{}

	for key, value := range mapA {
		node, found := mapB[key]
		if !found {
			mapAUnique = append(mapAUnique, node)
			continue
		}

		if value.data != node.data {
			mapADiffer = append(mapADiffer, []*polNode{value, node})
		}
	}

	for key, value := range mapB {
		node, found := mapA[key]
		if !found {
			mapBUnique = append(mapBUnique, node)
			continue
		}

		if value.data != node.data {
			mapBDiffer = append(mapBDiffer, []*polNode{value, node})
		}
	}

	// Return early if the maps are the same.
	if len(mapAUnique) <= 0 && len(mapBUnique) <= 0 && len(mapADiffer) <= 0 && len(mapBDiffer) <= 0 {
		return nil
	}

	var str string
	if len(mapAUnique) > 0 {
		str += fmt.Sprintf("Following nodes exist in mapA but does not in mapB:\n%s\n",
			printPolNodes(mapAUnique))
	}
	if len(mapBUnique) > 0 {
		str += fmt.Sprintf("Following nodes exist in mapB but does not in mapA:\n%s\n",
			printPolNodes(mapBUnique))
	}
	if len(mapADiffer) > 0 {
		keyStr := ""
		mapANodes := make([]*polNode, len(mapADiffer))
		mapBNodes := make([]*polNode, len(mapADiffer))
		for i, nodes := range mapADiffer {
			mHash := nodes[0].data.mini()
			keyStr += hex.EncodeToString(mHash[:])

			mapANodes[i] = nodes[0]
			mapBNodes[i] = nodes[1]
		}

		str += fmt.Sprintf("Keys:\n%s\nare differnt in mapA and mapB.\nMapA:\n%s\nMapB:\n%s\n",
			keyStr, printPolNodes(mapANodes), printPolNodes(mapBNodes))
	}
	if len(mapBDiffer) > 0 {
		keyStr := ""
		mapBNodes := make([]*polNode, len(mapADiffer))
		mapANodes := make([]*polNode, len(mapADiffer))
		for i, nodes := range mapADiffer {
			mHash := nodes[0].data.mini()
			keyStr += hex.EncodeToString(mHash[:])

			mapBNodes[i] = nodes[0]
			mapANodes[i] = nodes[1]
		}

		str += fmt.Sprintf("Keys:\n%s\nare differnt in mapB and mapA.\nMapB:\n%s\nMapA:\n%s\n",
			keyStr, printPolNodes(mapBNodes), printPolNodes(mapANodes))
	}

	return fmt.Errorf("%v", str)
}

func TestGetLeafPosition(t *testing.T) {
	type expectedRes struct {
		pos   uint64
		found bool
	}
	tests := []struct {
		p        Pollard
		mp       MapPollard
		hashes   []Hash
		expected []expectedRes
	}{
		{
			p: func() Pollard {
				p := NewAccumulator()
				leaves := make([]Leaf, 10)
				for i := range leaves {
					leaves[i] = Leaf{Hash: Hash{uint8(i + 1)}}
				}
				err := p.Modify(leaves, nil, Proof{})
				if err != nil {
					t.Fatal(err)
				}
				return p
			}(),
			mp: func() MapPollard {
				mp := NewMapPollard(true)
				leaves := make([]Leaf, 10)
				for i := range leaves {
					leaves[i] = Leaf{Hash: Hash{uint8(i + 1)}}
				}
				err := mp.Modify(leaves, nil, Proof{})
				if err != nil {
					t.Fatal(err)
				}
				return mp
			}(),
			hashes: []Hash{
				{1},
				{2},
				{3},
				{4},
				{5},
				{6},
				{7},
				{8},
				{9},
				{10},
				parentHash(Hash{1}, Hash{2}),
				parentHash(Hash{3}, Hash{4}),
				parentHash(Hash{5}, Hash{6}),
				parentHash(Hash{7}, Hash{8}),
				parentHash(Hash{9}, Hash{10}),
				parentHash(parentHash(Hash{1}, Hash{2}), parentHash(Hash{3}, Hash{4})),
				parentHash(parentHash(Hash{5}, Hash{6}), parentHash(Hash{7}, Hash{8})),
				parentHash(
					parentHash(parentHash(Hash{1}, Hash{2}), parentHash(Hash{3}, Hash{4})),
					parentHash(parentHash(Hash{5}, Hash{6}), parentHash(Hash{7}, Hash{8}))),
			},
			expected: []expectedRes{
				{0, true},
				{1, true},
				{2, true},
				{3, true},
				{4, true},
				{5, true},
				{6, true},
				{7, true},
				{8, true},
				{9, true},
				{0, false},
				{0, false},
				{0, false},
				{0, false},
				{0, false},
				{0, false},
				{0, false},
				{0, false},
			},
		},
	}

	testFn := func(hashes []Hash, expected []expectedRes, utreexo Utreexo) {
		// Test Pollard.
		for i, hash := range hashes {
			gotPosition, found := utreexo.GetLeafPosition(hash)
			if !found && expected[i].found {
				t.Fatalf("hash %v wasn't found", hash.String())
			}
			if !reflect.DeepEqual(gotPosition, expected[i].pos) {
				t.Fatalf("expected %v but got %v", expected[i].pos, gotPosition)
			}
		}
	}

	for _, test := range tests {
		// Test Pollard.
		testFn(test.hashes, test.expected, &test.p)

		// Test MapPollard.
		testFn(test.hashes, test.expected, &test.mp)
	}
}

func createPollards(full bool, duration uint32, seed int64) (*Pollard, *MapPollard, error) {
	// simulate blocks with simchain
	sc := newSimChainWithSeed(duration, seed)

	p := NewAccumulator()
	mp := NewMapPollard(full)
	for b := 0; b <= 100; b++ {
		adds, _, delHashes := sc.NextBlock(7)
		proof, err := p.Prove(delHashes)
		if err != nil {
			return nil, nil, err
		}

		err = p.Verify(delHashes, proof, false)
		if err != nil {
			return nil, nil, err
		}

		err = mp.Verify(delHashes, proof, false)
		if err != nil {
			return nil, nil, err
		}

		err = p.Modify(adds, delHashes, proof)
		if err != nil {
			return nil, nil, err
		}

		err = mp.Modify(adds, delHashes, proof)
		if err != nil {
			return nil, nil, err
		}
	}

	return &p, &mp, nil
}

func FuzzGetLeafPosition(f *testing.F) {
	var tests = []struct {
		numAdds  uint32
		duration uint32
		seed     int64
	}{
		{3, 0x07, 0x07},
	}
	for _, test := range tests {
		f.Add(test.numAdds, test.duration, test.seed)
	}

	f.Fuzz(func(t *testing.T, numAdds, duration uint32, seed int64) {
		p, mp, err := createPollards(true, duration, seed)
		if err != nil {
			t.Fatal(err)
		}

		for _, v := range p.NodeMap {
			expect := p.calculatePosition(v)
			got, found := mp.GetLeafPosition(v.data)
			if !found {
				t.Fatalf("expected to find hash %v in the "+
					"accumulator but didn't find it", v.data.String())
			}

			if expect != got {
				t.Fatalf("expected %v but got %v", expect, got)
			}
		}
	})
}
