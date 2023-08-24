package utreexo

import (
	"encoding/hex"
	"fmt"
	"math/rand"
	"reflect"
	"testing"
)

func FuzzStump(f *testing.F) {
	var tests = []struct {
		startLeaves uint32
		modifyAdds  uint32
		delCount    uint32
		seed        int64
	}{
		{
			8,
			2,
			3,
			0,
		},
		{
			6,
			2,
			5,
			0,
		},
		{
			16,
			4,
			10,
			0,
		},
		{
			16,
			6,
			14,
			424,
		},
	}
	for _, test := range tests {
		f.Add(test.startLeaves, test.modifyAdds, test.delCount, test.seed)
	}

	f.Fuzz(func(t *testing.T, startLeaves uint32, modifyAdds uint32, delCount uint32, seed int64) {
		t.Parallel()

		// Set seed to make sure the test is reproducible.
		rand.Seed(seed)

		// delCount must be less than the current number of leaves.
		if delCount > startLeaves {
			return
		}

		p := NewAccumulator(true)
		stump := Stump{}

		leaves, delHashes, _ := getAddsAndDels(uint32(p.NumLeaves), startLeaves, delCount)
		err := p.Modify(leaves, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}

		adds := make([]Hash, len(leaves))
		for i := range leaves {
			adds[i] = leaves[i].Hash
		}

		_, err = stump.Update(nil, adds, Proof{})
		if err != nil {
			t.Fatal(err)
		}

		// Check that the roots are the same after the addition.
		if len(p.Roots) != len(stump.Roots) {
			t.Fatalf("FuzzStump fail: jHave %d roots for pollard and %d roots for stump."+
				"\nStump:\n%s\nPollard:\n%s\n", len(p.Roots), len(stump.Roots),
				printHashes(stump.Roots), printPolNodes(p.Roots))
		}
		for i := range p.Roots {
			if p.Roots[i].data != stump.Roots[i] {
				t.Fatalf("FuzzStump fail: Roots do not equal between pollard and stump."+
					"\nStump:\n%s\nPollard:\n%s\n%s\n",
					printHashes(stump.Roots), printPolNodes(p.Roots), p.String())
			}
		}

		proof, err := p.Prove(delHashes)
		if err != nil {
			t.Fatal(err)
		}

		modifyLeaves, _, _ := getAddsAndDels(uint32(p.NumLeaves), 0, 0)
		err = p.Modify(modifyLeaves, delHashes, proof)
		if err != nil {
			t.Fatal(err)
		}

		// Save the roots before update.
		prevRoots := make([]Hash, len(stump.Roots))
		copy(prevRoots, stump.Roots)

		adds = make([]Hash, len(modifyLeaves))
		for i := range adds {
			adds[i] = modifyLeaves[i].Hash
		}
		// Update the stump.
		updateData, err := stump.Update(delHashes, adds, proof)
		if err != nil {
			t.Fatal(err)
		}

		err = checkUpdateData(updateData, adds, delHashes, prevRoots, proof, stump, &p)
		if err != nil {
			t.Fatalf("FuzzStump fail: error %v", err)
		}

		// Check that the roots are the same after addition/deletion.
		if len(p.Roots) != len(stump.Roots) {
			t.Fatalf("FuzzStump fail: jHave %d roots for pollard and %d roots for stump."+
				"\nStump:\n%s\nPollard:\n%s\n", len(p.Roots), len(stump.Roots),
				printHashes(stump.Roots), printPolNodes(p.Roots))
		}
		for i := range p.Roots {
			if p.Roots[i].data != stump.Roots[i] {
				t.Fatalf("FuzzStump fail: Roots do not equal between pollard and stump."+
					"\nStump:\n%s\nPollard:\n%s\n%s\n",
					printHashes(stump.Roots), printPolNodes(p.Roots), p.String())
			}
		}
	})
}

func FuzzStumpChain(f *testing.F) {
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

		p := NewAccumulator(true)
		stump := Stump{}

		var totalAdds, totalDels int
		for b := 0; b <= 100; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)
			totalAdds += len(adds)
			totalDels += len(delHashes)

			proof, err := p.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzStumpChain fail at block %d. Error: %v", b, err)
			}

			// Save the roots before update.
			prevRoots := make([]Hash, len(stump.Roots))
			copy(prevRoots, stump.Roots)

			addHashes := make([]Hash, len(adds))
			for i := range addHashes {
				addHashes[i] = adds[i].Hash
			}
			updateData, err := stump.Update(delHashes, addHashes, proof)
			if err != nil {
				t.Fatal(err)
			}

			err = p.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("FuzzStumpChain fail at block %d. Error: %v", b, err)
			}

			err = checkUpdateData(updateData, addHashes, delHashes, prevRoots, proof, stump, &p)
			if err != nil {
				t.Fatalf("FuzzStumpChain fail at block %d: error %v", b, err)
			}

			// Check that the roots are the same after addition/deletion.
			if len(p.Roots) != len(stump.Roots) {
				t.Fatalf("FuzzStumpChain fail at block %d: Have %d roots for pollard and %d roots for stump."+
					"\nStump:\n%s\nPollard:\n%s\n", b, len(p.Roots), len(stump.Roots),
					printHashes(stump.Roots), printPolNodes(p.Roots))
			}
			for i := range p.Roots {
				if p.Roots[i].data != stump.Roots[i] {
					t.Fatalf("FuzzStumpChain fail at block %d: Roots do not equal between pollard and stump."+
						"\nStump:\n%s\nPollard:\n%s\n%s\n", b,
						printHashes(stump.Roots), printPolNodes(p.Roots), p.String())
				}
			}
		}
	})
}

// checkUpdateData makes sure tha the information given in the updateData is valid.
func checkUpdateData(updateData UpdateData, adds, delHashes, prevRoots []Hash, proof Proof, stump Stump, p *Pollard) error {
	/*
	 * First check the validity of the prevNumLeaves and ToDestory fields
	 * in the update data.
	 */
	if updateData.PrevNumLeaves != stump.NumLeaves-uint64(len(adds)) {
		err := fmt.Errorf("Expected update data to have "+
			"PrevNumLeaves of %d, but got %d",
			stump.NumLeaves-uint64(len(adds)), updateData.PrevNumLeaves)
		return err
	}
	for _, destroyed := range updateData.ToDestroy {
		node, _, _, err := p.getNode(destroyed)
		if err == nil && node != nil {
			if node.data == empty {
				err := fmt.Errorf("Expected empty root of %d to be deleted.\n"+
					"Roots:\n%s\n", destroyed, printHashes(p.GetRoots()))
				return err
			}
		}
	}

	/*
	 * Then check the validity of the addition and deletions fields in the updateData.
	 */
	// Attach the hashes to their positions.
	targetsWithHash := toHashAndPos(proof.Targets, delHashes)
	proofPos, _ := proofPositions(targetsWithHash.positions, updateData.PrevNumLeaves, treeRows(updateData.PrevNumLeaves))
	proofWithPositions := toHashAndPos(proofPos, proof.Proof)

	// Update accordingly.
	proofIdx, targetsIdx := 0, 0
	for i, hash := range updateData.NewDelHash {
		pos := updateData.NewDelPos[i]

		for proofIdx < proofWithPositions.Len() && proofWithPositions.positions[proofIdx] < pos {
			proofIdx++
		}
		if proofIdx < proofWithPositions.Len() && proofWithPositions.positions[proofIdx] == pos {
			proofWithPositions.hashes[proofIdx] = hash
		}

		for targetsIdx < targetsWithHash.Len() && targetsWithHash.positions[targetsIdx] < pos {
			targetsIdx++
		}
		if targetsIdx < targetsWithHash.Len() && targetsWithHash.positions[targetsIdx] == pos {
			targetsWithHash.hashes[targetsIdx] = hash
		}
	}

	// Calculate the modified roots after the remove.
	intermediate, roots := calculateHashes(updateData.PrevNumLeaves,
		targetsWithHash.hashes, Proof{targetsWithHash.positions, proofWithPositions.hashes})

	// Check that the intermidate hashes and positions are the same.
	if !reflect.DeepEqual(intermediate, hashAndPos{updateData.NewDelPos, updateData.NewDelHash}) {
		err := fmt.Errorf("Intermediate hashes and positions are different\n"+
			"UpdateData:\n%s\nCalcaluted:\n%s\n",
			hashAndPos{updateData.NewDelPos, updateData.NewDelHash}.String(),
			intermediate.String())
		return err
	}

	rootIndexes, err := Verify(Stump{prevRoots, updateData.PrevNumLeaves}, delHashes, proof)
	if err != nil {
		return err
	}
	// Replace with new roots.
	for i, index := range rootIndexes {
		prevRoots[index] = roots[i]
	}
	// Then add.
	stumpCopy := Stump{prevRoots, updateData.PrevNumLeaves}
	calcHash, calcPos, calcToDestroy := stumpCopy.add(adds)

	// Check that the new hashes and positions are the same.
	if !reflect.DeepEqual(hashAndPos{calcPos, calcHash}, hashAndPos{updateData.NewAddPos, updateData.NewAddHash}) {
		err := fmt.Errorf("Newly added hashes and positions are different\n"+
			"UpdateData:\n%s\nCalcaluted:\n%s\n",
			hashAndPos{updateData.NewAddPos, updateData.NewAddHash}.String(),
			hashAndPos{calcPos, calcHash}.String())
		return err
	}
	// Check that the new adds and hashes exist and are equal as the pollard.
	for i, hash := range updateData.NewAddHash {
		pos := updateData.NewAddPos[i]

		gotHash := p.getHash(pos)
		if gotHash != hash {
			err := fmt.Errorf("For pos %d, expected %s but got %s",
				pos, hex.EncodeToString(gotHash[:]), hex.EncodeToString(hash[:]))
			return err
		}
	}
	// Check that toDestroy is the same.
	if !reflect.DeepEqual(calcToDestroy, updateData.ToDestroy) {
		err := fmt.Errorf("Calculated toDestroy is different\n"+
			"UpdateData:\n%v\nCalcaluted:\n%v\n",
			updateData.ToDestroy, calcToDestroy)
		return err
	}

	// Check that the roots are the same after addition/deletion.
	if len(p.Roots) != len(stumpCopy.Roots) {
		err := fmt.Errorf("Have %d roots for pollard and %d roots for stump."+
			"\nStump:\n%s\nPollard:\n%s\n", len(p.Roots), len(stump.Roots),
			printHashes(stump.Roots), printPolNodes(p.Roots))
		return err
	}
	for i := range p.Roots {
		if p.Roots[i].data != stumpCopy.Roots[i] {
			err := fmt.Errorf("Roots do not equal between pollard and stump."+
				"\nStump:\n%s\nPollard:\n%s\n%s\n",
				printHashes(stump.Roots), printPolNodes(p.Roots), p.String())
			return err
		}
	}

	return nil
}
