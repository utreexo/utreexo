package utreexo

// Utreexo defines the interface that all consensus abiding Utreexo implementations
// should have.
type Utreexo interface {
	Modify(adds []Leaf, delHashes []Hash, proof Proof) error
	Prove(delHashes []Hash) (Proof, error)
	Verify(delHashes []Hash, proof Proof, remember bool) error
	Undo(numAdds uint64, proof Proof, delHashes, prevRoots []Hash) error

	GetRoots() []Hash
	GetHash(position uint64) Hash
	GetNumLeaves() uint64
	GetTreeRows() uint8
	String() string
}

type Bridge interface {
	Utreexo1
	//Lookup(outpoints []outpoints) ([]uint64, error)
}

type Utreexo1 interface {
	Modify(adds []Leaf, delHashes []Hash, proof Proof) error
	Prove(positions []uint64) (Proof, error)
	Verify(delHashes []Hash, proof Proof, Remember bool) error
	Forget(position uint64)
	Undo(numAdds uint64, proof Proof, delHashes, prevRoots []Hash) error

	GetRoots() []Hash
	GetHash(position uint64) Hash
	GetNumLeaves() uint64
	GetTreeRows() uint8
	String() string
}
