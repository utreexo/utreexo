package utreexo

import (
	"fmt"

	"github.com/utreexo/utreexo/internal/rowwalk"
	"golang.org/x/exp/slices"
)

// ForestSnapshot is the per-block view a proof-generation pass operates on: the
// cumulative leaf count at that block and the deleted-leaf bitmap to mask
// against. RehashAndProve reads layout and masking only through the snapshot,
// never the live forest fields, so a pass is pinned to one block's state even
// while the record stage advances NumLeaves for later blocks.
//
// In the IBD pipeline the snapshot's bitmap is the forest's own: the generate
// stage is its sole writer and rehashes blocks in record order, so it holds the
// deletions in force as of numLeaves. The snapshot is the unit a future
// concurrent generator would carry per block, each with its own bitmap version.
type ForestSnapshot struct {
	numLeaves uint64
	deleted   *deletedBitmap
}

// Snapshot captures the forest's per-block proof-generation view at numLeaves.
// The caller passes the leaf count it recorded for the block being proved
// rather than letting the pass read the live NumLeaves.
func (f *Forest) Snapshot(numLeaves uint64) ForestSnapshot {
	return ForestSnapshot{numLeaves: numLeaves, deleted: f.deletedLeafPositions}
}

// RehashAndProve regenerates the forest roots and, in the same deletion walk,
// captures the inclusion proof for pendingDels.
//
// The sibling hashes the walk reads while recomputing deletion-path parents are
// the proof hashes, so the proof falls out of the walk without a separate
// traversal of the file.
//
// Appended leaves are rehashed before the deletion walk, so a sibling the walk
// reads on an add path is already final. The walk writes each deletion-path
// parent last, overwriting whatever the add pass left at that position, so the
// masking of deleted leaves carries all the way to the roots.
//
// snap is the per-block view (see ForestSnapshot): the leaf count the roots are
// laid out over and the bitmap the walk masks against. The pass reads both from
// the snapshot, so the record stage advancing NumLeaves for later blocks cannot
// bias this one.
//
// pendingDels must be deletion positions Record returned, each passed to
// exactly one successful RehashAndProve call. RehashAndProve sets their deleted
// bits at the start of the pass and masks them as it walks, so the bitmap
// reflects exactly the blocks rehashed so far and a later block's deletions
// never bias this one. The forest counts these deletions awaiting their masking
// walk to know when the interior hashes are fully caught up, and the count
// stays accurate only under that one-call pairing. A call that returns an error
// consumes nothing. Pass the same pendingDels again once the fault is cleared,
// and re-running the walk overwrites its earlier partial writes with the same
// values.
func (f *Forest) RehashAndProve(snap ForestSnapshot, pendingDels []uint64) ([]Hash, uint64, Proof, error) {
	// A read lock, not the write lock: this pass and a concurrent Record touch
	// disjoint forest state. This pass owns the bitmap, the interior rows and
	// the generated-leaves counters; Record owns positionMap, the leaf row and
	// NumLeaves. The cache mutex and pipelineMu cover what both reach. Only one
	// generate stage runs at a time, so the pass-owned fields need no extra
	// guard here.
	f.mu.RLock()
	defer f.mu.RUnlock()

	// Interior hashes are rewritten below; keep the generated-leaves slot
	// cleared until the pass completes so an error return cannot leave a
	// completeness claim over a half-rebuilt file.
	if err := f.clearGeneratedLeaves(); err != nil {
		return nil, 0, Proof{}, fmt.Errorf("clear generated leaves: %w", err)
	}

	// Mark this block's deletions at the moment its proof pass runs. Record
	// leaves the bitmap untouched, so a block's bits become visible exactly
	// here, both for the add pass that masks created-then-spent leaves and for
	// the deletion walk below. The set is idempotent, so a retry after an error
	// re-marks the same positions harmlessly.
	for _, pos := range pendingDels {
		snap.deleted.set(pos)
	}

	totalLeaves := snap.numLeaves
	forestRows := f.forestRows

	fromLeaves := f.lastGeneratedLeaves
	if fromLeaves == 0 || fromLeaves > totalLeaves {
		fromLeaves = 0
	}
	if err := f.processAddsParallel(fromLeaves, totalLeaves, forestRows, snap.deleted); err != nil {
		return nil, 0, Proof{}, err
	}

	proof, err := f.rehashDeletionsAndCaptureProof(pendingDels, totalLeaves, forestRows, snap.deleted)
	if err != nil {
		return nil, 0, Proof{}, err
	}

	roots, numLeaves, err := f.getRoots(totalLeaves, snap.deleted)
	if err != nil {
		return nil, 0, Proof{}, err
	}

	// Update the counters only after every step that can fail. An earlier
	// error returned without touching them, so the caller can pass the same
	// pendingDels again and the retry counts them exactly once.
	f.lastGeneratedLeaves = totalLeaves
	// This pass masked the pendingDels it was given, so subtract them from the
	// outstanding count Record raised when it recorded the block. Record marks
	// no bits, so a from-scratch pass (fromLeaves == 0) still masks only the
	// deletions whose bits a pass has set, i.e. this block's, which is why the
	// subtraction is unconditional. min keeps the unsigned count from
	// underflowing if a caller re-passes positions an earlier pass already
	// masked.
	f.pipelineMu.Lock()
	prevUnmasked := f.unmaskedDels
	f.unmaskedDels -= min(f.unmaskedDels, uint64(len(pendingDels)))
	f.pipelineMu.Unlock()
	if err := f.saveGeneratedLeaves(); err != nil {
		f.pipelineMu.Lock()
		f.unmaskedDels = prevUnmasked
		f.pipelineMu.Unlock()
		return nil, 0, Proof{}, fmt.Errorf("save generated leaves: %w", err)
	}

	return roots, numLeaves, proof, nil
}

// rehashDeletionsAndCaptureProof rehashes the deletion paths of pendingDels and
// assembles their inclusion proof. Walking row by row, sibling pairs that are
// both deleted collapse into a single parent computation; an entry whose
// sibling is not also deleted is "lone", and that sibling's stored hash is a
// proof hash for the verifier.
//
// The returned proof's Targets are pendingDels sorted ascending (translated to
// defaultForestRows when the forest uses a different row count). Proof hashes
// are ordered by row, then by position within the row, as calculateHashes
// expects.
func (f *Forest) rehashDeletionsAndCaptureProof(pendingDels []uint64, numLeaves uint64, forestRows uint8, deleted *deletedBitmap) (Proof, error) {
	if len(pendingDels) == 0 {
		return Proof{}, nil
	}

	affected, targets := sortedDeletionTargets(pendingDels, forestRows)

	// Starting capacity only: a deletion path contributes one proof hash per
	// row where it is lone, so clustered deletions need almost none while
	// scattered ones need several per target; append grows the slice past this.
	proofHashes := make([]Hash, 0, len(pendingDels))

	for row := uint8(0); row < forestRows && len(affected) > 0; row++ {
		parents, rowProof, err := f.rehashDeletionRow(affected, row, numLeaves, forestRows, deleted)
		if err != nil {
			return Proof{}, err
		}
		proofHashes = append(proofHashes, rowProof...)

		affected = rowwalk.DropMarked(parents)
	}

	return Proof{Targets: targets, Proof: proofHashes}, nil
}

// sortedDeletionTargets returns pendingDels sorted ascending, along with the
// proof targets: the same positions translated to defaultForestRows when the
// forest uses a different row count.
func sortedDeletionTargets(pendingDels []uint64, forestRows uint8) (affected, targets []uint64) {
	affected = make([]uint64, len(pendingDels))
	copy(affected, pendingDels)
	slices.SortFunc(affected, uint64Less)

	targets = make([]uint64, len(affected))
	copy(targets, affected)
	if forestRows != defaultForestRows {
		targets = translatePositions(targets, forestRows, defaultForestRows)
	}
	return affected, targets
}

// rehashDeletionRow recomputes the parent of every entry in affected for one
// row, writing the new parent hashes to the file, and returns those parent
// positions. The right half of a sibling pair is recorded with
// rowwalk.MarkRedundant — its left half records the shared parent — and a root
// entry, which has no parent, with rowwalk.MarkRoot. For each lone entry — one
// whose sibling is not also in affected — it also returns the sibling hash it
// read; those are the proof hashes for this row, in ascending position order.
// A sibling past the row's last occupied position contributes an empty hash
// without touching the file, so a read error is a real I/O fault and aborts
// the row.
func (f *Forest) rehashDeletionRow(affected []uint64, row uint8, numLeaves uint64, forestRows uint8, deleted *deletedBitmap) ([]uint64, []Hash, error) {
	n := len(affected)
	parents := make([]uint64, n)
	proofSlots := make([]Hash, n)
	hasProof := make([]bool, n)

	// The row's last occupied position. A sibling past it does not exist, so
	// its hash is empty by position arithmetic rather than by a file read.
	maxPos, err := maxPositionAtRow(row, forestRows, numLeaves)
	if err != nil {
		return nil, nil, err
	}

	// runRowWork calls work with index windows [s, e) that partition [0, n):
	// one inline (0, n) call for a small row, or disjoint windows running
	// concurrently on the pool workers for a large one. The windows tile the
	// range — each begins where the previous one ends, from 0 through n — so
	// every index is processed exactly once, and runRowWork returns only after
	// every window has run.
	work := func(s, e int) error {
		for i := s; i < e; i++ {
			pos := affected[i]

			// The right half of a sibling pair is redundant: its left half
			// computes the shared parent. affected is ascending, so the
			// halves are adjacent, and the check only looks backward — a
			// window that starts on a right half still sees its twin at i-1.
			if i > 0 && affected[i-1] == leftSib(pos) {
				rowwalk.MarkRedundant(parents, i)
				continue
			}

			if isRootPositionTotalRows(pos, numLeaves, forestRows) {
				// A deleted leaf that is itself a root keeps its hash in the
				// slot, matching deleteSingle: every reader masks the
				// position through the deleted bitmap, the position map
				// verifies its entries against the slot, and Undo restores
				// the root from the preserved hash.
				rowwalk.MarkRoot(parents, i)
				continue
			}

			currentHash, err := f.readHashForProof(pos, deleted)
			if err != nil {
				return err
			}

			// pos is lone when its sibling is not also on the deletion path,
			// making that sibling's stored hash a proof hash for the
			// verifier. The forward look mirrors the backward skip above: a
			// processed entry's pair can only sit directly after it.
			lone := i+1 >= n || affected[i+1] != rightSib(pos)

			sibPos := sibling(pos)
			var sibHash Hash
			if sibPos > maxPos {
				sibHash = empty
			} else {
				h, err := f.readHashForProof(sibPos, deleted)
				if err != nil {
					return err
				}
				sibHash = h
			}

			if lone {
				proofSlots[i] = sibHash
				hasProof[i] = true
			}

			parentPos := Parent(pos, forestRows)
			var newHash Hash
			if isLeftNiece(pos) {
				newHash = parentHash(currentHash, sibHash)
			} else {
				newHash = parentHash(sibHash, currentHash)
			}
			if err := f.writeHashAt(parentPos, newHash); err != nil {
				return err
			}
			parents[i] = parentPos
		}
		return nil
	}

	if err := runRowWork(n, work); err != nil {
		return nil, nil, err
	}

	proof := make([]Hash, 0, n)
	for i := 0; i < n; i++ {
		if hasProof[i] {
			proof = append(proof, proofSlots[i])
		}
	}
	return parents, proof, nil
}

// processAddsParallel rebuilds the interior hashes for the leaves appended
// between prevLeaves and totalLeaves, walking each affected position up to its
// root one row at a time. At every row the rehash collapses each appended
// sibling pair to a single parent computation; the per-row work is fanned
// across the pipeline worker pool once a row reaches minParallelSize.
func (f *Forest) processAddsParallel(prevLeaves, totalLeaves uint64, forestRows uint8, deleted *deletedBitmap) error {
	numAdds := int(totalLeaves - prevLeaves)
	if numAdds == 0 {
		return nil
	}

	affected := make([]uint64, numAdds)
	for i := range affected {
		affected[i] = prevLeaves + uint64(i)
	}

	parents := make([]uint64, numAdds)
	nextAffected := make([]uint64, 0, numAdds)

	for row := uint8(0); row < forestRows && len(affected) > 0; row++ {
		var err error
		parents, err = f.rehashAddRow(affected, parents, row, totalLeaves, forestRows, deleted)
		if err != nil {
			return err
		}

		nextAffected = rowwalk.CollectNext(parents, nextAffected)
		affected, nextAffected = nextAffected, affected
	}

	return nil
}

// rehashAddRow recomputes the parent of every appended position in affected
// for one row, writing each new parent hash to the file, and returns those
// parent positions. The right half of a sibling pair is recorded with
// rowwalk.MarkRedundant — its left half records the shared parent — and a root
// position, which has no parent, with rowwalk.MarkRoot. On the leaf row a
// sibling marked deleted contributes an empty hash, and a right sibling past
// the row's last occupied position contributes an empty hash without touching
// the file, so a read error is a real I/O fault and aborts the row. parents is
// grown when too small and reused as the result buffer to avoid a per-row
// allocation.
func (f *Forest) rehashAddRow(affected, parents []uint64, row uint8, totalLeaves uint64, forestRows uint8, deleted *deletedBitmap) ([]uint64, error) {
	n := len(affected)
	if cap(parents) < n {
		parents = make([]uint64, n)
	}
	parents = parents[:n]

	// The row's last occupied position. A right sibling past it does not
	// exist, so its hash is empty by position arithmetic rather than by a
	// file read. Left siblings are always occupied: rows fill contiguously
	// from their start, and lPos <= pos.
	maxPos, err := maxPositionAtRow(row, forestRows, totalLeaves)
	if err != nil {
		return nil, err
	}

	// runRowWork calls work with index windows [s, e) that partition [0, n):
	// one inline (0, n) call for a small row, or disjoint windows running
	// concurrently on the pool workers for a large one. The windows tile the
	// range — each begins where the previous one ends, from 0 through n — so
	// every index is processed exactly once, and runRowWork returns only after
	// every window has run.
	work := func(s, e int) error {
		for i := s; i < e; i++ {
			pos := affected[i]

			// The right half of a sibling pair is redundant: its left half
			// computes the shared parent. affected is ascending, so the
			// halves are adjacent, and the check only looks backward — a
			// window that starts on a right half still sees its twin at i-1.
			if i > 0 && affected[i-1] == leftSib(pos) {
				rowwalk.MarkRedundant(parents, i)
				continue
			}

			if isRootPositionTotalRows(pos, totalLeaves, forestRows) {
				rowwalk.MarkRoot(parents, i)
				continue
			}

			lPos := leftSib(pos)
			rPos := rightSib(pos)

			var leftHash, rightHash Hash
			if row == 0 && deleted.isSet(lPos) {
				leftHash = empty
			} else {
				h, err := f.readHashAt(lPos)
				if err != nil {
					return err
				}
				leftHash = h
			}

			if rPos > maxPos {
				rightHash = empty
			} else if row == 0 && deleted.isSet(rPos) {
				rightHash = empty
			} else {
				h, err := f.readHashAt(rPos)
				if err != nil {
					return err
				}
				rightHash = h
			}

			parentPos := Parent(pos, forestRows)
			newHash := parentHash(leftHash, rightHash)

			if err := f.writeHashAt(parentPos, newHash); err != nil {
				return err
			}
			parents[i] = parentPos
		}
		return nil
	}

	if err := runRowWork(n, work); err != nil {
		return nil, err
	}
	return parents, nil
}

// runRowWork applies work to the index range [0, n) of one row's positions.
// Rows at or above minParallelSize are split across the pipeline worker pool;
// smaller rows run inline to avoid the dispatch overhead. It returns the first
// error any worker reports.
func runRowWork(n int, work func(start, end int) error) error {
	if n < minParallelSize {
		return work(0, n)
	}
	errs := make([]error, numWorkers)
	pipelineParallelDo(func(wIdx, s, e int) {
		errs[wIdx] = work(s, e)
	}, n)
	for _, err := range errs {
		if err != nil {
			return err
		}
	}
	return nil
}

// readHashForProof reads the hash at position, returning empty for a deleted
// leaf on the leaf row. Non-leaf rows always read from the file.
func (f *Forest) readHashForProof(position uint64, deleted *deletedBitmap) (Hash, error) {
	if DetectRow(position, f.forestRows) == 0 && deleted.isSet(position) {
		return empty, nil
	}
	return f.readHashAt(position)
}

// readHashAt reads the hash at the given position. Uses the value-typed HashAt
// to keep the result on the caller's stack frame; routing through io.ReaderAt
// forces the buffer to escape to the heap.
func (f *Forest) readHashAt(position uint64) (Hash, error) {
	return f.file.HashAt(f.posToFileOffset(position))
}

// writeHashAt writes the hash at the given position. Uses the value-typed
// PutHashAt to avoid the heap allocation that an io.WriterAt-typed slice would
// force on the caller.
func (f *Forest) writeHashAt(position uint64, hash Hash) error {
	return f.file.PutHashAt(hash, f.posToFileOffset(position))
}
