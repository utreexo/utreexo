package utreexo

import (
	"bytes"
	"encoding/hex"
	"fmt"
	"math/rand"
	"reflect"
	"testing"
)

func (m *MapPollard) nodeMapToString() string {
	return "n/a"
}

func (m *MapPollard) rootToString() string {
	return printHashes(m.GetRoots())
}

func (m *MapPollard) sanityCheck() error {
	err := m.checkPruned()
	if err != nil {
		return err
	}
	err = m.checkProofNodes()
	if err != nil {
		return err
	}

	return m.checkHashes()
}

func (m *MapPollard) checkPruned() error {
	neededPos := make(map[uint64]struct{})
	for _, v := range m.CachedLeaves {
		for _, pos := range proofPosition(v, m.NumLeaves, m.TotalRows) {
			neededPos[pos] = struct{}{}
		}
		neededPos[v] = struct{}{}
	}

	for _, pos := range rootPositions(m.NumLeaves, m.TotalRows) {
		neededPos[pos] = struct{}{}
	}

	for k, v := range m.Nodes {
		_, found := neededPos[k]
		if !found {
			return fmt.Errorf("Have node %s at pos %d in map even though it's not needed",
				v, k)
		}
	}

	return nil
}

// checkProofNodes checks that all the proof positions needed to cache a proof exists in the map
// of nodes.
func (m *MapPollard) checkProofNodes() error {
	// Sanity check.
	for k, v := range m.CachedLeaves {
		leaf, found := m.Nodes[v]
		if !found {
			return fmt.Errorf("Corrupted pollard. Missing cached leaf at %d", v)
		}

		if k != leaf.Hash {
			return fmt.Errorf("Corrupted pollard. Pos %d cached hash: %s, but have %s",
				v, k, leaf.Hash)
		}

		proofPos := proofPosition(v, m.NumLeaves, m.TotalRows)
		for _, pos := range proofPos {
			_, found := m.Nodes[pos]
			if !found {
				return fmt.Errorf("Corrupted pollard. Missing pos %d "+
					"needed for proving %d", pos, v)
			}
		}
	}

	return nil
}

// checkHashes checks that the leaves correctly hash up to the roots. Returns an error if
// any of the roots or the intermediate nodes don't match up with the calculated hashes.
func (m *MapPollard) checkHashes() error {
	if len(m.CachedLeaves) == 0 {
		return nil
	}

	leafHashes := make([]Hash, 0, len(m.CachedLeaves))
	for leafHash := range m.CachedLeaves {
		leafHashes = append(leafHashes, leafHash)
	}

	proof, err := m.Prove(leafHashes)
	if err != nil {
		return err
	}

	if m.TotalRows != treeRows(m.NumLeaves) {
		for i := range proof.Targets {
			proof.Targets[i] = translatePos(proof.Targets[i], m.TotalRows, treeRows(m.NumLeaves))
		}
	}

	haveRoots, rootPositions := m.getRoots()
	rootIndexes, err := Verify(Stump{Roots: haveRoots, NumLeaves: m.NumLeaves}, leafHashes, proof)
	if err != nil {
		//fmt.Println("m.cachedLeaves: ", m.CachedLeaves)
		return fmt.Errorf("Failed to verify proof:\n%s\ndelHashes:\n%s\nerr: %v\n", proof.String(), printHashes(leafHashes), err)
	}

	// Check roots.
	intermediate, gotRoots := calculateHashes(m.NumLeaves, leafHashes, proof)
	if len(gotRoots) != len(rootIndexes) {
		return fmt.Errorf("expected %d calculated roots but got %d", len(gotRoots), len(rootIndexes))
	}

	for i, rootIdx := range rootIndexes {
		if haveRoots[rootIdx] != gotRoots[i] {
			return fmt.Errorf("For root position %d, calculated %s but have %s",
				rootPositions[i], hex.EncodeToString(gotRoots[i][:]),
				hex.EncodeToString(haveRoots[rootIdx][:]))
		}
	}

	// Check all intermediate nodes.
	for i, pos := range intermediate.positions {
		haveNode, found := m.Nodes[pos]
		if !found {
			continue
		}
		gotHash := intermediate.hashes[i]

		if haveNode.Hash != gotHash {
			return fmt.Errorf("For position %d, calculated %s but have %s",
				pos, hex.EncodeToString(gotHash[:]), hex.EncodeToString(haveNode.Hash[:]))
		}
	}

	return nil
}

func FuzzMapPollard(f *testing.F) {
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
		// delCount must be less than the current number of leaves.
		if delCount > startLeaves {
			return
		}

		acc := NewMapPollard()
		leaves, delHashes, delTargets := getAddsAndDels(uint32(acc.NumLeaves), startLeaves, delCount)
		err := acc.Modify(leaves, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}
		beforeStr := String(&acc)

		proof, err := acc.Prove(delHashes)
		if err != nil {
			fmt.Printf("m.Cached:\n%v\ndelHashes:\n%s\nLeaves:\n%s\n",
				acc.CachedLeaves, printHashes(delHashes), printLeaves(leaves))
			t.Fatal(err)
		}
		proof.Targets = delTargets

		modifyLeaves, _, _ := getAddsAndDels(uint32(acc.NumLeaves), modifyAdds, 0)
		err = acc.Modify(modifyLeaves, delHashes, proof)
		if err != nil {
			t.Fatal(err)
		}
		afterStr := String(&acc)

		accFull := NewAccumulator(true)
		err = accFull.Modify(leaves, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}

		beforeFullStr := String(&accFull)
		err = accFull.Modify(modifyLeaves, delHashes, proof)
		if err != nil {
			t.Fatal(err)
		}

		err = acc.checkHashes()
		if err != nil {
			retErr := fmt.Errorf("FuzzMapPollard fail: %v. "+
				"\nbefore:\n\n%s"+
				"\nafter:\n\n%s"+
				"\nbefore full:\n\n%s"+
				"\nafter full:\n\n%s"+
				"\nstartLeaves %d, modifyAdds %d, delCount %d, "+
				"\nstartLeaves:\n%s"+
				"\nmodifyLeaves:\n%s"+
				"\nmodifyDels:\n%s"+
				"\ncachedLeaves:\n%v"+
				"\ndel targets:\n%v",
				err,
				beforeStr,
				afterStr,
				beforeFullStr,
				String(&accFull),
				startLeaves, modifyAdds, delCount,
				printLeaves(leaves),
				printLeaves(modifyLeaves),
				printHashes(delHashes),
				acc.CachedLeaves,
				delTargets)
			t.Fatal(retErr)
		}

		err = acc.checkProofNodes()
		if err != nil {
			t.Fatal(err)
		}

		// Compare the roots.
		expectHashes := accFull.GetRoots()
		gotHashes := acc.GetRoots()
		for i := range expectHashes {
			if expectHashes[i] != gotHashes[i] {
				err := fmt.Errorf("expected roots:\n%s\ngot:\n%s\n",
					printHashes(expectHashes), printHashes(gotHashes))
				retErr := fmt.Errorf("FuzzMapPollard fail: %v"+
					"\nbefore:\n\n%s"+
					"\nafter:\n\n%s"+
					"\naccFull before:\n\n%s"+
					"\naccFull:\n\n%s"+
					"\nstartLeaves %d, modifyAdds %d, delCount %d, "+
					"\nstartLeaves:\n%s"+
					"\nmodifyLeaves:\n%s"+
					"\nmodifyDels:\n%s"+
					"\ncachedLeaves:\n%v"+
					"\ndel targets:\n%v",
					err,
					beforeStr,
					afterStr,
					beforeFullStr,
					String(&accFull),
					startLeaves, modifyAdds, delCount,
					printLeaves(leaves),
					printLeaves(modifyLeaves),
					printHashes(delHashes),
					acc.CachedLeaves,
					delTargets)
				t.Fatal(retErr)
			}
		}
	})
}

func (p *Proof) checkEqualProof(other Proof) error {
	if len(other.Targets) != len(p.Targets) {
		return fmt.Errorf("Have %d targets but other has %d targets. mine: %v, other: %v",
			len(p.Targets), len(other.Targets), p.Targets, other.Targets)
	}

	for i := range p.Targets {
		if p.Targets[i] != other.Targets[i] {
			return fmt.Errorf("At idx %d have %d but other has %d. sorted mine: %v, sorted other: %v",
				i, p.Targets[i], other.Targets[i], p.Targets, other.Targets)
		}
	}

	if len(other.Proof) != len(p.Proof) {
		return fmt.Errorf("Have %d proof but other has %d proof.\nMine:\n%s\nother:\n%s\n",
			len(p.Proof), len(other.Proof), printHashes(p.Proof), printHashes(other.Proof))
	}

	for i := range p.Proof {
		if p.Proof[i] != other.Proof[i] {
			return fmt.Errorf("At idx %d have %s but other has %s.\nMine:\n%s\nother:\n%s\n",
				i, p.Proof[i], other.Proof[i], printHashes(p.Proof), printHashes(other.Proof))
		}
	}

	return nil
}

func FuzzMapPollardChain(f *testing.F) {
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

		m := NewMapPollard()
		if numAdds&1 == 1 {
			m.TotalRows = 50
		}
		full := NewAccumulator(true)

		var totalAdds, totalDels int
		for b := 0; b <= 50; b++ {
			adds, _, delHashes := sc.NextBlock(numAdds)
			totalAdds += len(adds)
			totalDels += len(delHashes)

			expectProof, err := full.Prove(delHashes)
			if err != nil {
				t.Fatal(err)
			}

			err = m.Verify(delHashes, expectProof, true)
			if err != nil {
				t.Fatalf("%v\nproving delHashes:\nproof:\n%s\n%s\nmap:\n%s\nfull:\n%s\n",
					err, printHashes(delHashes), expectProof.String(),
					String(&m), String(&full))
			}

			proof, err := m.Prove(delHashes)
			if err != nil {
				fmt.Println("prove failacc:\n", String(&m))
				t.Fatalf("FuzzMapPollardChain fail at block %d. Couldn't prove\n%s\nError: %v",
					b, printHashes(delHashes), err)
			}

			err = proof.checkEqualProof(expectProof)
			if err != nil {
				t.Fatalf("\nFor delhashes: %v\nexpected proof:\n%s\ngot:\n%s\nerr: %v\n"+
					"maptreexo:\n%s\nfull:\n%s\n",
					printHashes(delHashes), expectProof.String(), proof.String(), err,
					String(&m), String(&full))
			}

			for _, target := range proof.Targets {
				fetch := target
				if m.TotalRows != treeRows(m.NumLeaves) {
					fetch = translatePos(fetch, treeRows(m.NumLeaves), m.TotalRows)
				}
				hash := m.GetHash(fetch)
				if hash == empty {
					t.Fatalf("FuzzMapPollardChain doesn't have the hash "+
						"for %d at block %d.", target, b)
				}
			}

			err = m.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("FuzzMapPollardChain fail at block %d. Error: %v", b, err)
			}

			err = full.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatal(err)
			}

			cachedHashes := make([]Hash, 0, len(m.CachedLeaves))
			leafHashes := make([]Hash, 0, len(m.CachedLeaves))
			for hash := range m.CachedLeaves {
				cachedHashes = append(cachedHashes, hash)
				leafHashes = append(leafHashes, hash)
			}

			if !reflect.DeepEqual(cachedHashes, leafHashes) {
				err := fmt.Errorf("Fail at block %d. For cachedLeaves of %v\ngot cachedHashes:\n%s\n"+
					"leafHashes:\n%s\nmaptreexo:\n%s\nfull:\n%s\n",
					b, m.CachedLeaves, printHashes(cachedHashes), printHashes(leafHashes),
					String(&m), String(&full))
				t.Fatal(err)
			}

			cachedProofExpect, err := full.Prove(cachedHashes)
			if err != nil {
				t.Fatal(err)
			}

			cachedProof, err := m.Prove(leafHashes)
			if err != nil {
				t.Fatal(err)
			}

			if m.TotalRows != treeRows(m.NumLeaves) {
				for i := range cachedProof.Targets {
					cachedProof.Targets[i] = translatePos(
						cachedProof.Targets[i], m.TotalRows, treeRows(m.NumLeaves))
				}
			}

			err = cachedProof.checkEqualProof(cachedProofExpect)
			if err != nil {
				t.Fatalf("\nFor delhashes: %v\nexpected proof:\n%s\ngot:\n%s\nerr: %v\n"+
					"maptreexo:\n%s\nfull:\n%s\n",
					printHashes(cachedHashes), cachedProofExpect.String(), cachedProof.String(),
					err, String(&m), String(&full))
			}

			fullRoots := full.GetRoots()
			mapRoots := m.GetRoots()
			if !reflect.DeepEqual(fullRoots, mapRoots) {
				t.Fatalf("Roots differ. expected:\n%s\nbut got:\n%s\nfull:\n%s\nmap:\n%s\n",
					printHashes(fullRoots), printHashes(mapRoots), String(&full), String(&m))
			}

			err = m.checkHashes()
			if err != nil {
				t.Fatal(err)
			}

			err = m.checkProofNodes()
			if err != nil {
				t.Fatal(err)

			}

			err = m.checkPruned()
			if err != nil {
				t.Fatal(err)
			}
		}
	})
}

func FuzzMapPollardWriteAndRead(f *testing.F) {
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

		m := NewMapPollard()
		for b := 0; b <= 20; b++ {
			adds, durations, delHashes := sc.NextBlock(numAdds)
			for i, duration := range durations {
				if duration != 0 {
					adds[i].Remember = true
				}
			}

			proof, err := m.Prove(delHashes)
			if err != nil {
				t.Fatalf("FuzzWriteAndRead fail at block %d. Error: %v", b, err)
			}

			err = m.Modify(adds, delHashes, proof)
			if err != nil {
				t.Fatalf("FuzzWriteAndRead fail at block %d. Error: %v", b, err)
			}
		}
		err := m.checkHashes()
		if err != nil {
			t.Fatal(err)
		}

		var buf bytes.Buffer
		wroteBytes, err := m.Write(&buf)
		if err != nil {
			t.Fatal(err)
		}

		if wroteBytes != len(buf.Bytes()) {
			t.Fatalf("FuzzWriteAndRead Fail. Wrote %d but serializeSize got %d",
				wroteBytes, len(buf.Bytes()))
		}

		m1 := NewMapPollard()

		// Restore from the buffer.
		readBytes, err := m1.Read(&buf)
		if err != nil {
			t.Fatal(err)
		}
		if readBytes != wroteBytes {
			t.Fatalf("FuzzWriteAndRead Fail. Wrote %d but read %d", readBytes, wroteBytes)
		}

		// Check that the hashes of the roots are correct.
		err = m1.checkHashes()
		if err != nil {
			t.Fatal(err)
		}
	})
}
