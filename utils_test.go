package utreexo

import (
	"fmt"
	"math/rand"
	"reflect"
	"sort"
	"testing"
	"time"

	"golang.org/x/exp/slices"
)

func TestProofPosition(t *testing.T) {
	t.Parallel()

	var tests = []struct {
		position  uint64
		numLeaves uint64
		totalRows uint8
	}{
		{numLeaves: 2, totalRows: 50},
		{numLeaves: 2, totalRows: 1},
		{numLeaves: 15, totalRows: 50},
		{numLeaves: 4454546, totalRows: 50},
	}

	for _, test := range tests {
		got := proofPosition(test.position, test.numLeaves, test.totalRows)
		expect, _ := ProofPositions([]uint64{test.position}, test.numLeaves, test.totalRows)

		if !reflect.DeepEqual(got, expect) {
			t.Fatalf("expected %v, got %v for numleaves %d, totalrows %d",
				expect, got, test.numLeaves, test.totalRows)
		}
	}
}

func TestInForest(t *testing.T) {
	t.Parallel()

	var tests = []struct {
		position  uint64
		numLeaves uint64
		totalRows uint8
		expect    bool
	}{
		{position: 0, numLeaves: 2, totalRows: 50, expect: true},
		{position: 4, numLeaves: 2, totalRows: 50, expect: false},
		{position: 5, numLeaves: 2, totalRows: 50, expect: false},
		{position: 35, numLeaves: 40, totalRows: 50, expect: true},
		{position: 43, numLeaves: 40, totalRows: 50, expect: false},
		{position: Parent(59, 50), numLeaves: 40, totalRows: 50, expect: false},

		{position: 150_004, numLeaves: 152_121, totalRows: 50, expect: true},
		{position: 156_004, numLeaves: 152_121, totalRows: 50, expect: false},
		{position: Parent(156_004, 50), numLeaves: 152_121, totalRows: 50, expect: false},
		{position: Parent(Parent(156_004, 50), 50), numLeaves: 152_121, totalRows: 50, expect: false},
	}

	for _, test := range tests {
		got := inForest(test.position, test.numLeaves, test.totalRows)
		if test.expect != got {
			t.Fatalf("Expected %v but got %v for position:%d, numleaves:%d",
				test.expect, got, test.position, test.numLeaves)
		}

		// Sanity check.
		row := DetectRow(test.position, test.totalRows)
		max, err := maxPositionAtRow(row, test.totalRows, test.numLeaves)
		if err != nil {
			t.Fatal(err)
		}
		if got && test.position > max {
			t.Fatalf("Expected %v but got %v for position:%d, numleaves:%d",
				false, got, test.position, test.numLeaves)
		}
		if !got && test.position <= max {
			t.Fatalf("Expected %v but got %v for position:%d, numleaves:%d",
				true, got, test.position, test.numLeaves)
		}
	}
}

func TestRootPositions(t *testing.T) {
	t.Parallel()

	var tests = []struct {
		numLeaves uint64
		totalRows uint8
	}{
		{numLeaves: 2, totalRows: 50},
		{numLeaves: 2, totalRows: 1},
		{numLeaves: 15, totalRows: 50},
		{numLeaves: 4454546, totalRows: 50},
		{numLeaves: 4454546, totalRows: TreeRows(4454546)},
		{numLeaves: 111875, totalRows: 50},
		{numLeaves: 111875, totalRows: TreeRows(111875)},
	}

	for _, test := range tests {
		roots := RootPositions(test.numLeaves, test.totalRows)

		for i := range roots {
			root := roots[i]
			if !isRootPositionTotalRows(root, test.numLeaves, test.totalRows) {
				t.Errorf("Calculated %d is not a root for numleaves:%d, totalrows:%d",
					root, test.numLeaves, test.totalRows)
			}
		}
	}
}

func TestIsRootPositionTotalRows(t *testing.T) {
	t.Parallel()

	var tests = []struct {
		position  uint64
		numLeaves uint64
		totalRows uint8
		expect    bool
	}{
		// 02
		// |---\
		// 00  01
		{position: 0, numLeaves: 2, totalRows: 50, expect: false},
		{position: 1, numLeaves: 2, totalRows: 50, expect: false},
		{position: Parent(0, 50), numLeaves: 2, totalRows: 50, expect: true},

		// |-------\
		// 04
		// |---\   |---\
		// 00  01  02
		{position: 0, numLeaves: 3, totalRows: 50, expect: false},
		{position: 1, numLeaves: 3, totalRows: 50, expect: false},
		{position: 2, numLeaves: 3, totalRows: 50, expect: true},
		{position: 3, numLeaves: 3, totalRows: 50, expect: false},
		{position: Parent(0, 50), numLeaves: 3, totalRows: 50, expect: true},
	}

	for _, test := range tests {
		got := isRootPositionTotalRows(test.position, test.numLeaves, test.totalRows)
		if test.expect != got {
			t.Fatalf("Expected %v but got %v for position:%d, numleaves:%d",
				test.expect, got, test.position, test.numLeaves)
		}
	}
}

func TestIsRootPosition(t *testing.T) {
	t.Parallel()

	var tests = []struct {
		position  uint64
		numLeaves uint64
		expect    bool
	}{
		// 02
		// |---\
		// 00  01
		{position: 0, numLeaves: 2, expect: false},
		{position: 1, numLeaves: 2, expect: false},
		{position: 2, numLeaves: 2, expect: true},

		// |-------\
		// 04
		// |---\   |---\
		// 00  01  02
		{position: 0, numLeaves: 3, expect: false},
		{position: 1, numLeaves: 3, expect: false},
		{position: 2, numLeaves: 3, expect: true},
		{position: 3, numLeaves: 3, expect: false},
		{position: 4, numLeaves: 3, expect: true},
	}

	for _, test := range tests {
		got := isRootPosition(test.position, test.numLeaves)
		if test.expect != got {
			t.Fatalf("Expected %v but got %v for position:%d, numleaves:%d",
				test.expect, got, test.position, test.numLeaves)
		}
	}
}

func TestTranslatePos(t *testing.T) {
	t.Parallel()

	var tests = []struct {
		position uint64
		fromRows uint8
		toRows   uint8
		expected uint64
	}{
		// From:
		//
		// 06
		// |-------\
		// 04      05
		// |---\   |---\
		// 00  01  02  03
		//
		// To:
		//
		// |---------------\
		// 12
		// |-------\       |-------\
		// 08      09
		// |---\   |---\   |---\   |---\
		// 00  01  02  03
		//
		// Row 0 tests.
		{position: 0, fromRows: 2, toRows: 3, expected: 0},
		{position: 1, fromRows: 2, toRows: 3, expected: 1},
		{position: 2, fromRows: 2, toRows: 3, expected: 2},
		{position: 3, fromRows: 2, toRows: 3, expected: 3},
		{position: 0, fromRows: 3, toRows: 2, expected: 0},
		{position: 1, fromRows: 3, toRows: 2, expected: 1},
		{position: 2, fromRows: 3, toRows: 2, expected: 2},
		{position: 3, fromRows: 3, toRows: 2, expected: 3},
		//
		// Row 1 tests.
		{position: 4, fromRows: 2, toRows: 3, expected: 8},
		{position: 5, fromRows: 2, toRows: 3, expected: 9},
		{position: 8, fromRows: 3, toRows: 2, expected: 4},
		{position: 9, fromRows: 3, toRows: 2, expected: 5},
		//
		// Row 2 tests.
		{position: 6, fromRows: 2, toRows: 3, expected: 12},
		{position: 12, fromRows: 3, toRows: 2, expected: 6},

		// From:
		//
		// 06
		// |-------\
		// 04      05
		// |---\   |---\
		// 00  01  02  03
		//
		//
		// To:
		//
		// |-------------------------------\
		//
		// |---------------\               |---------------\
		// 24
		// |-------\       |-------\       |-------\       |-------\
		// 16      17
		// |---\   |---\   |---\   |---\   |---\   |---\   |---\   |---\
		// 00  01  02  03
		//
		// Row 0 tests.
		{position: 0, fromRows: 2, toRows: 4, expected: 0},
		{position: 1, fromRows: 2, toRows: 4, expected: 1},
		{position: 2, fromRows: 2, toRows: 4, expected: 2},
		{position: 3, fromRows: 2, toRows: 4, expected: 3},
		{position: 0, fromRows: 4, toRows: 2, expected: 0},
		{position: 1, fromRows: 4, toRows: 2, expected: 1},
		{position: 2, fromRows: 4, toRows: 2, expected: 2},
		{position: 3, fromRows: 4, toRows: 2, expected: 3},
		//
		// Row 1 tests.
		{position: 4, fromRows: 2, toRows: 4, expected: 16},
		{position: 5, fromRows: 2, toRows: 4, expected: 17},
		{position: 16, fromRows: 4, toRows: 2, expected: 4},
		{position: 17, fromRows: 4, toRows: 2, expected: 5},
		//
		// Row 2 tests.
		{position: 6, fromRows: 2, toRows: 4, expected: 24},
		{position: 24, fromRows: 4, toRows: 2, expected: 6},
	}

	for i, test := range tests {
		got := translatePos(test.position, test.fromRows, test.toRows)
		if got != test.expected {
			t.Errorf("test #%d, for position %d, fromRow %d, toRow %d, "+
				"expected %d, got %d", i, test.position, test.fromRows,
				test.toRows, test.expected, got)
		}
	}
}

func TestChildMany(t *testing.T) {
	t.Parallel()

	var tests = []struct {
		position  uint64
		drop      uint8
		totalRows uint8
		expected  uint64
		err       error
	}{
		// 06
		// |-------\
		// 04      05
		// |---\   |---\
		// 00  01  02  03
		{position: 4, drop: 1, totalRows: 2, expected: 0, err: nil},
		{position: 6, drop: 2, totalRows: 2, expected: 0, err: nil},
		{position: 6, drop: 0, totalRows: 2, expected: 6, err: nil},
		{position: 5, drop: 0, totalRows: 2, expected: 5, err: nil},
		{position: 5, drop: 1, totalRows: 2, expected: 2, err: nil},
		{position: 6, drop: 3, totalRows: 2, expected: 0, err: fmt.Errorf("drop of %d is greater than forestRows of %d", 3, 2)},

		// 14
		// |---------------\
		// 12              13
		// |-------\       |-------\
		// 08      09      10      11
		// |---\   |---\   |---\   |---\
		// 00  01  02  03  04  05  06  07
		{position: 13, drop: 2, totalRows: 3, expected: 04, err: nil},
		{position: 13, drop: 0, totalRows: 3, expected: 13, err: nil},
		{position: 13, drop: 4, totalRows: 3, expected: 0, err: fmt.Errorf("drop of %d is greater than forestRows of %d", 4, 3)},
		{position: 12, drop: 0, totalRows: 3, expected: 12, err: nil},
		{position: 12, drop: 1, totalRows: 3, expected: 8, err: nil},
		{position: 12, drop: 2, totalRows: 3, expected: 0, err: nil},
	}

	for _, test := range tests {
		got, err := ChildMany(test.position, test.drop, test.totalRows)
		if err != nil {
			if test.err == nil {
				t.Errorf("expected error of %v but got %v", test.err, err)
			}
		}

		if got != test.expected {
			t.Errorf("expected %v but got %v", test.expected, got)
		}
	}
}

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
