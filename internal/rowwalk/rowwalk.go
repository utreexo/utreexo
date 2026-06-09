// Package rowwalk holds the per-row position-list operations used while the
// forest rehashes a row of nodes up to the row above. A row's parent slice can
// contain slots that carry no real position — a node that is already a root has
// no parent to walk upward, and the right half of a sibling pair is redundant
// because its left half records the shared parent. Those slots are filled with
// an unexported tombstone value that never leaves this package: MarkRoot and
// MarkRedundant fill them, and CollectNext and DropMarked drop them, so the rest
// of the forest never sees the sentinel as if it were a position.
package rowwalk

// tombstone fills a slot that carries no real position: a node that is already
// a root has no parent to recompute (MarkRoot), and the right half of a sibling
// pair is redundant (MarkRedundant). Every reader — CollectNext and DropMarked —
// drops it; keeping it unexported is what stops it from being mistaken for a
// position elsewhere. ^uint64(0) is safe as the marker because it is the one
// uint64 value position arithmetic cannot produce: uint64 positions cap a
// forest at 63 rows, the topmost root of a 63-row forest sits at 2^64-2, and
// the only parent computation that would wrap to 2^64-1 — the parent of that
// root — is exactly the case producers intercept with MarkRoot.
const tombstone = ^uint64(0)

// MarkRoot records that parents[i] carries no parent position because the node
// it was derived from is already a root. CollectNext and DropMarked drop the
// slots MarkRoot fills.
func MarkRoot(parents []uint64, i int) {
	parents[i] = tombstone
}

// MarkRedundant records that parents[i] carries no parent position because the
// node it was derived from is the right half of a sibling pair: the left
// half's slot records the pair's shared parent. CollectNext and DropMarked drop
// the slots MarkRedundant fills.
func MarkRedundant(parents []uint64, i int) {
	parents[i] = tombstone
}

// CollectNext gathers the live parent positions from parents into dst (reused
// across rows), dropping the marked slots, to become the set of positions
// walked on the next row up. parents must already be sorted ascending: nothing
// here sorts or dedupes — order is preserved, and the sibling-pair skip on the
// next row needs ascending input. Parents of an ascending row are strictly
// ascending on their own: a parent position is non-decreasing in the child
// position, and only siblings — whose right halves are marked redundant rather
// than walked — share one.
func CollectNext(parents, dst []uint64) []uint64 {
	dst = dst[:0]
	for i := 0; i < len(parents); i++ {
		if parents[i] != tombstone {
			dst = append(dst, parents[i])
		}
	}
	return dst
}

// DropMarked compacts positions in place, dropping the marked slots, and
// returns the trimmed slice. positions must already be sorted ascending:
// nothing here sorts or dedupes — order is preserved, and the sibling-pair
// skip on the next row needs ascending input.
func DropMarked(positions []uint64) []uint64 {
	j := 0
	for i := 0; i < len(positions); i++ {
		if positions[i] != tombstone {
			positions[j] = positions[i]
			j++
		}
	}
	return positions[:j]
}
