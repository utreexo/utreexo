package utreexo

// Utreexo defines the interface that all consensus abiding Utreexo implementations
// should have.
type Utreexo interface {
	// Modify subtracts then adds elements to the accumulator. The deletions are done in batches
	// so if.
	Modify(adds []Leaf, delHashes []Hash, proof Proof) error

	// Prove returns a proof of the given hashes.
	Prove(delHashes []Hash) (Proof, error)

	// Verify returns an error if the given hashes and proof hash up to a different root than
	// the one the accumulator has.  Remember flag of true will tell the accumulator to cache
	// the proof if it is valid.
	Verify(delHashes []Hash, proof Proof, remember bool) error

	// Undo reverts a modification done by Modify.
	Undo(prevAdds []Hash, proof Proof, delHashes, prevRoots []Hash) error

	// GetRoots returns the current roots of the accumulator.
	GetRoots() []Hash

	// GetHash returns the hash at the given position. Returns an empty hash if the position either
	// doesn't exist or if the position is not cached.
	GetHash(position uint64) Hash

	// GetLeafPosition returns the position for the given leaf hash. The boolean returns false if the
	// hash wasn't found.
	//
	// NOTE It always returns false for any non-leaf hashes.
	GetLeafPosition(Hash) (uint64, bool)

	// GetNumLeaves returns the number of total additions the accumulator has ever had.
	GetNumLeaves() uint64

	// GetTreeRows returns the current tree rows the accumulator has allocated for.
	GetTreeRows() uint8

	// String returns a string representation of the accumulator only if the result of GetTreeRows
	// is less than 7. Will return the hash of roots instead if the accumulator is too tall.
	String() string
}
