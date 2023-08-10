package utreexo

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"math/rand"
	"reflect"
	"testing"
)

// Assert that Pollard implements the UtreexoTest interface.
var _ UtreexoTest = (*Pollard)(nil)

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
			v := NewAccumulator(true)
			utreexo = &v
		}
		adds := make([]Leaf, len(test.startAdds))
		for i := range adds {
			hash := test.startAdds[i]
			adds[i] = Leaf{Hash: hash}
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
		err = utreexo.Undo(uint64(len(test.modifyAdds)), modifyProof, test.modifyDels, beforeRoots)
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
	totalRows := treeRows(p.NumLeaves)

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
		p := NewAccumulator(true)
		fuzzModify(t, &p, startLeaves, modifyAdds, delCount)
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

	modifyLeaves, _, _ := getAddsAndDels(uint32(p.GetNumLeaves()), modifyAdds, 0)
	err = p.Modify(modifyLeaves, delHashes, Proof{Targets: delTargets})
	if err != nil {
		t.Fatal(err)
	}
	afterStr := p.String()
	afterMap := p.nodeMapToString()

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
			"\nnodemap after modify:\n %s",
			err,
			beforeStr,
			afterStr,
			startLeaves, modifyAdds, delCount,
			printHashes(startHashes),
			printHashes(modifyHashes),
			printHashes(delHashes),
			delTargets,
			beforeMap,
			afterMap)
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
		// simulate blocks with simchain
		sc := newSimChainWithSeed(duration, seed)

		p := NewAccumulator(true)
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
		fuzzUndo(t, &Pollard{}, startLeaves, modifyAdds, delCount)
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
		v := NewAccumulator(true)
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

	err = p.Undo(uint64(modifyAdds), bp, dels, beforeRoots)
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
		// We have to do this because the fuzz will give process hung or
		// terminated unexpectedly error.
		numBlocks := uint32(100)
		if numAdds > 500 {
			numBlocks = 30
		}

		p := NewAccumulator(true)
		fuzzUndoChain(t, &p, numBlocks, numAdds, duration, seed)
	})
}

func fuzzUndoChain(t *testing.T, p UtreexoTest, blockCount, numAdds, duration uint32, seed int64) {
	full := NewAccumulator(true)

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
			if treeRows(p.GetNumLeaves()) != p.GetTreeRows() {
				gotHash = p.GetHash(translatePos(bp.Targets[i], treeRows(p.GetNumLeaves()), p.GetTreeRows()))
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

		// Undo the last 10 modifies and re-do them.
		if b%10 == 9 {
			for i := 9; i >= 0; i-- {
				copyProof := Proof{Targets: make([]uint64, len(undoData[i].proof.Targets)), Proof: make([]Hash, len(undoData[i].proof.Proof))}
				copy(copyProof.Targets, undoData[i].proof.Targets)
				copy(copyProof.Proof, undoData[i].proof.Proof)

				err := p.Undo(uint64(len(undoData[i].adds)), copyProof, undoData[i].hashes, undoData[i].prevRoots)
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

			// Sanity check after the undos.
			err = p.sanityCheck()
			if err != nil {
				t.Fatal(err)
			}

			// Undo the undos.
			for i := 0; i < 10; i++ {
				adds, delHashes := undoData[i].adds, undoData[i].hashes

				bp := undoData[i].proof
				err = p.Verify(delHashes, bp, true)
				if err != nil {
					t.Fatal(err)
				}
				err = p.Modify(adds, delHashes, bp)
				if err != nil {
					t.Fatalf("FuzzUndoChain fail at block %d. Error: %v", b, err)
				}
			}

			// Sanity check after undoing the undos.
			err = p.sanityCheck()
			if err != nil {
				t.Fatal(err)
			}
			undoData = undoData[:0]
		}
	}

	// Sanity check after it's all finished.
	err := p.sanityCheck()
	if err != nil {
		t.Fatal(err)
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
		rand.Seed(seed)

		// simulate blocks with simchain
		sc := newSimChainWithSeed(duration, seed)

		p := NewAccumulator(true)
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

	return fmt.Errorf(str)
}

// Test that the cached nodes are correct.
func TestProofCacheNodes(t *testing.T) {

	// Create a new accumulator with 10 leaves.
	adds := make([]Leaf, 10)
	for i := range adds {
		adds[i] = Leaf{Hash: sha256.Sum256([]byte{uint8(i)})}
	}

	// Create the accumulator and add one leaf at a time.
	p := NewAccumulator(true)
	for _, leaf := range adds {
		err := p.Modify([]Leaf{leaf}, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}
	}

	fmt.Printf("Merkle tree:\n\n%s\n", p.String())

	// Check that the nodes are cached correctly.
	for i := range adds {
		fmt.Printf("For node at position: %x\n", i)
		leaves, _, err := p.getNodesForProof(uint64(i))
		if err != nil {
			fmt.Print("hre")
			fmt.Printf("error: %x\n", i)
			t.Fatal(err)
		}

		// Leaf hashes that should be cached ideally
		cachedLeaves := []Leaf{}
		for _, leaf := range leaves {
			if leaf.Remember {
				cachedLeaves = append(cachedLeaves, leaf)
			}
		}
		cachedLeavesHash := []string{}
		for i := range cachedLeaves {
			cachedLeavesHash = append(cachedLeavesHash, fmt.Sprintf("%x", cachedLeaves[i].Hash))
		}
		fmt.Printf("Hash of leaves that should be cached:\n")
		fmt.Print(cachedLeavesHash)

		// Leaf hashes that are actually cached
		proof, err := p.Prove([]Hash{p.getHash(uint64(i))})
		if err != nil {
			fmt.Println("Error generating proof:", err)
			return
		}
		var actualCaches []string
		for _, p := range proof.Proof {
			var hexString string
			for _, b := range p {
				hexString += hex.EncodeToString([]byte{b})
			}
			actualCaches = append(actualCaches, hexString)
		}
		fmt.Print("\nHash of leaves that are actually cached:\n")
		fmt.Println(actualCaches)

		// Check that the cached nodes match.
		for i := range cachedLeavesHash {
			if cachedLeavesHash[i] != actualCaches[i] {
				fmt.Printf("Error: cached node %d does not match (expected %s, got %s)\n", i, cachedLeavesHash[i], actualCaches[i])
				continue
			}
		}

		fmt.Printf("All cached nodes match for leaf: %x\n\n", i)
	}
}
