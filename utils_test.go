package utreexo

import (
	"fmt"
	"math/rand"
	"sort"
	"testing"
	"time"

	"golang.org/x/exp/slices"
)

func TestDeTwin(t *testing.T) {
	t.Parallel()

	var tests = []struct {
		forestRows uint8
		before     []uint64
		expected   []uint64
	}{
		{3, []uint64{0, 1, 9}, []uint64{12}},
		{3, []uint64{0, 1, 4, 9, 11}, []uint64{4, 11, 12}},
		{3, []uint64{0, 1, 2, 3, 4, 11}, []uint64{4, 11, 12}},
		{4, []uint64{0, 1, 4, 6, 10, 11, 17, 20}, []uint64{4, 6, 24, 26}},
		{4, []uint64{8, 9, 10, 24, 25}, []uint64{10, 20, 28}},
		{4, []uint64{0, 2, 18, 19, 21, 27}, []uint64{0, 2, 21, 25, 27}},
		{4, []uint64{0, 1, 2, 3, 5, 13, 14, 15}, []uint64{5, 13, 23, 24}},
	}

	for _, test := range tests {
		test.before = deTwin(test.before, test.forestRows)

		if len(test.before) != len(test.expected) {
			t.Errorf("TestDeTwin Error: expected %d elements but got %d",
				len(test.expected), len(test.before))
		}

		for i := range test.before {
			if test.before[i] != test.expected[i] {
				t.Errorf("TestDeTwin Error: expected %v but got %v",
					test.expected, test.before)
			}
		}
	}
}

func TestDeTwinRand(t *testing.T) {
	t.Parallel()

	seed := time.Now().Unix()
	rand.Seed(seed)

	for x := 0; x < 100000; x++ {
		// Forest with at least 3 rows but less than 11 rows.
		forestRows := uint8(rand.Intn(11-3) + 3)

		// Maximum position the accumulator can have.
		maxPosition := (1 << forestRows) - 1
		delAmount := 10
		if maxPosition < 10 {
			delAmount = rand.Intn(maxPosition)
		}

		// Generate the dels randomly.
		dels := make([]uint64, 0, delAmount)
		for i := 0; i < delAmount; i++ {
			randNum := uint64(rand.Intn(maxPosition))
			for slices.Contains(dels, randNum) {
				randNum = uint64(rand.Intn(maxPosition))
			}

			dels = append(dels, randNum)
		}

		sort.Slice(dels, func(a, b int) bool { return dels[a] < dels[b] })
		origDels := make([]uint64, len(dels))
		copy(origDels, dels)

		dels = deTwin(dels, forestRows)

		// Check that there are no siblings in the del slice.
		for i := 0; i < len(dels); i++ {
			if i+1 < len(dels) && rightSib(dels[i]) == dels[i+1] {
				err := fmt.Errorf("TestDeTwinRand error: seed %v, forestRows %v, "+
					"dels[i]=%d and dels[i+1]=%d are siblings. "+
					"Original: %v, deTwined: %v",
					seed, forestRows, dels[i], dels[i+1], origDels, dels)
				t.Fatal(err)
			}
		}
	}
}

//func TestIsRootPosition(t *testing.T) {
//	var tests = []struct {
//		position  uint64
//		numLeaves uint64
//		totalRows uint8
//		expect    bool
//	}{
//		{position: 2, numLeaves: 2, totalRows: 1}, //fmt.Println(isRootPosition(2, 2, 1)),
//	}
//
//	for _, test := range tests {
//		got := isRootPosition(test.position, test.numLeaves, test.totalRows)
//		if test.expect != got {
//			t.Fatalf("Expected %v but got %v for position:%d, numleaves:%d, totalrows:%d",
//				test.expect, got, test.position, test.numLeaves, test.totalRows)
//		}
//	}
//}
