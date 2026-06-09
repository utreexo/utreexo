package utreexo

import (
	"github.com/utreexo/utreexo/internal/rowwalk"
)

// processAddsParallel rebuilds the interior hashes for the leaves appended
// between prevLeaves and totalLeaves, walking each affected position up to its
// root one row at a time. At every row the rehash collapses each appended
// sibling pair to a single parent computation; the per-row work is fanned
// across the pipeline worker pool once a row reaches minParallelSize.
func (f *Forest) processAddsParallel(prevLeaves, totalLeaves uint64, forestRows uint8) error {
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
		parents, err = f.rehashAddRow(affected, parents, row, totalLeaves, forestRows)
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
func (f *Forest) rehashAddRow(affected, parents []uint64, row uint8, totalLeaves uint64, forestRows uint8) ([]uint64, error) {
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
			if row == 0 && f.deletedLeafPositions.isSet(lPos) {
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
			} else if row == 0 && f.deletedLeafPositions.isSet(rPos) {
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
