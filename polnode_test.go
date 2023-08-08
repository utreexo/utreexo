package utreexo

import (
	"encoding/hex"
	"fmt"
	"testing"
)

func TestCalculatePosition(t *testing.T) {
	t.Parallel()

	var tests = []struct {
		adds     []Leaf
		dels     []uint64
		expected map[Hash]uint64
	}{
		{
			[]Leaf{
				{Hash: Hash{1}},
				{Hash: Hash{2}},
				{Hash: Hash{3}},
				{Hash: Hash{4}},
				{Hash: Hash{5}},
				{Hash: Hash{6}},
				{Hash: Hash{7}},
				{Hash: Hash{8}},
			},
			nil,
			map[Hash]uint64{
				{1}: 0,
				{2}: 1,
				{3}: 2,
				{4}: 3,
				{5}: 4,
				{6}: 5,
				{7}: 6,
				{8}: 7,
			},
		},
		{
			[]Leaf{
				{Hash: Hash{1}},
				{Hash: Hash{2}},
				{Hash: Hash{3}},
				{Hash: Hash{4}},
				{Hash: Hash{5}},
				{Hash: Hash{6}},
				{Hash: Hash{7}},
				{Hash: Hash{8}},
			},
			[]uint64{0},
			map[Hash]uint64{
				{2}: 8,
				{3}: 2,
				{4}: 3,
				{5}: 4,
				{6}: 5,
				{7}: 6,
				{8}: 7,
			},
		},
	}

	for _, test := range tests {
		p := NewAccumulator(true)

		err := p.Modify(test.adds, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}

		err = p.Modify(nil, nil, Proof{Targets: test.dels})
		if err != nil {
			t.Fatal(err)
		}

		for hash, pos := range test.expected {
			node, found := p.NodeMap[hash.mini()]
			if !found {
				err := fmt.Errorf("TestCalculatePosition error: "+
					"expected node with hash of %s not found",
					hex.EncodeToString(hash[:]))
				t.Fatal(err)
			}

			calculated := p.calculatePosition(node)
			if calculated != pos {
				err := fmt.Errorf("TestCalculatePosition error: "+
					"for node with hash %s, expected %d, got %d",
					hex.EncodeToString(hash[:]), pos, calculated)
				t.Fatal(err)
			}
		}
	}
}

func TestReadPosition(t *testing.T) {
	t.Parallel()

	var tests = []struct {
		adds     []Leaf
		dels     []uint64
		expected map[Hash]uint64
	}{
		{
			[]Leaf{
				{Hash: Hash{1}},
				{Hash: Hash{2}},
				{Hash: Hash{3}},
				{Hash: Hash{4}},
				{Hash: Hash{5}},
				{Hash: Hash{6}},
				{Hash: Hash{7}},
				{Hash: Hash{8}},
			},
			[]uint64{0},
			map[Hash]uint64{
				{3}: 2,
				{4}: 3,
				{5}: 4,
				{6}: 5,
				{7}: 6,
				{8}: 7,
				{2}: 8,
			},
		},
		{
			[]Leaf{
				{Hash: Hash{1}},
				{Hash: Hash{2}},
				{Hash: Hash{3}},
				{Hash: Hash{4}},
				{Hash: Hash{5}},
				{Hash: Hash{6}},
				{Hash: Hash{7}},
				{Hash: Hash{8}},
			},
			[]uint64{0, 4, 5, 7},
			map[Hash]uint64{
				{3}: 2,
				{4}: 3,
				{2}: 8,
				{7}: 13,
			},
		},
	}
	for _, test := range tests {
		p := NewAccumulator(true)

		err := p.Modify(test.adds, nil, Proof{})
		if err != nil {
			t.Fatal(err)
		}

		err = p.Modify(nil, nil, Proof{Targets: test.dels})
		if err != nil {
			t.Fatal(err)
		}

		for hash, pos := range test.expected {
			n, _, _, err := p.getNode(pos)
			if err != nil {
				t.Fatal(err)
			}

			if n.data != hash {
				err := fmt.Errorf("TestReadPosition error: "+
					"for pos %d, expected %s, got %s",
					pos, hex.EncodeToString(hash[:]),
					hex.EncodeToString(n.data[:]))
				t.Fatal(err)
			}

		}
	}
}
