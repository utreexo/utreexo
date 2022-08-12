package utreexo

import (
	"math/rand"
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
		// Set seed to make sure the test is reproducible.
		rand.Seed(seed)

		// delCount must be less than the current number of leaves.
		if delCount > startLeaves {
			return
		}

		p := NewAccumulator(true)
		stump := Stump{}

		leaves, delHashes, _ := getAddsAndDels(uint32(p.NumLeaves), startLeaves, delCount)
		err := p.Modify(leaves, nil, nil)
		if err != nil {
			t.Fatal(err)
		}

		adds := make([]Hash, len(leaves))
		for i := range leaves {
			adds[i] = leaves[i].Hash
		}

		err = stump.Update(nil, adds, Proof{})
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
		err = p.Modify(modifyLeaves, delHashes, proof.Targets)
		if err != nil {
			t.Fatal(err)
		}

		adds = make([]Hash, len(modifyLeaves))
		for i := range adds {
			adds[i] = modifyLeaves[i].Hash
		}

		err = stump.Update(delHashes, adds, proof)
		if err != nil {
			t.Fatal(err)
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

			addHashes := make([]Hash, len(adds))
			for i := range addHashes {
				addHashes[i] = adds[i].Hash
			}
			err = stump.Update(delHashes, addHashes, proof)
			if err != nil {
				t.Fatal(err)
			}

			err = p.Modify(adds, delHashes, proof.Targets)
			if err != nil {
				t.Fatalf("FuzzStumpChain fail at block %d. Error: %v", b, err)
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
