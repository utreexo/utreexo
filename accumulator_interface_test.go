package utreexo

// UtreexoTest extends the Utreexo interface by adding on a few extra methods that are only useful
// during testing.
type UtreexoTest interface {
	// Utreexo is the underlying Utreexo interface.
	Utreexo

	// sanityCheck checks for inconsistencies in the accumulator.
	sanityCheck() error

	// nodeMapToString returns the node map as a string. empty string or "n/a" if
	// the implementation doesn't have a node map.
	nodeMapToString() string

	// rootToString returns the roots as a string.
	rootToString() string
}
