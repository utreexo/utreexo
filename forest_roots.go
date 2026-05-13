package utreexo

import (
	"fmt"

	"golang.org/x/exp/slices"
)

func (f *Forest) processAddsParallel(snap *ForestView, prevLeaves, totalLeaves uint64, forestRows uint8) error {
	numAdds := int(totalLeaves - prevLeaves)
	if numAdds == 0 {
		return nil
	}

	affected := make([]uint64, numAdds)
	for i := range affected {
		affected[i] = prevLeaves + uint64(i)
	}

	parentOut := make([]uint64, numAdds)
	nextAffected := make([]uint64, 0, numAdds)
	errs := make([]error, numWorkers)

	for row := uint8(0); row < forestRows && len(affected) > 0; row++ {
		n := len(affected)

		for i := 0; i < n-1; i++ {
			if affected[i] == ^uint64(0) {
				continue
			}
			if affected[i]^1 == affected[i+1] {
				affected[i] = leftSib(affected[i])
				affected[i+1] = ^uint64(0)
			}
		}
		j := 0
		for i := 0; i < n; i++ {
			if affected[i] != ^uint64(0) {
				affected[j] = affected[i]
				j++
			}
		}
		affected = affected[:j]
		n = j
		if n == 0 {
			break
		}

		if cap(parentOut) < n {
			parentOut = make([]uint64, n)
		}
		parentOut = parentOut[:n]

		processAddsWork := func(s, e int) error {
			for i := s; i < e; i++ {
				pos := affected[i]

				if isRootPositionTotalRows(pos, totalLeaves, forestRows) {
					parentOut[i] = ^uint64(0)
					continue
				}

				lPos := leftSib(pos)
				rPos := lPos | 1

				var leftHash, rightHash Hash
				if row == 0 && snap.bitmap.isSet(lPos) {
					leftHash = empty
				} else {
					h, err := f.readHashAt(lPos)
					if err != nil {
						leftHash = empty
					} else {
						leftHash = h
					}
				}

				if row == 0 && snap.bitmap.isSet(rPos) {
					rightHash = empty
				} else {
					h, err := f.readHashAt(rPos)
					if err != nil {
						rightHash = empty
					} else {
						rightHash = h
					}
				}

				parentPos := Parent(pos, forestRows)
				newHash := parentHash(leftHash, rightHash)

				if err := f.writeHashAt(parentPos, newHash); err != nil {
					return err
				}
				parentOut[i] = parentPos
			}
			return nil
		}

		if n < minParallelSize {
			if err := processAddsWork(0, n); err != nil {
				return err
			}
		} else {
			for i := range errs {
				errs[i] = nil
			}
			pipelineParallelDo(func(wIdx, s, e int) {
				errs[wIdx] = processAddsWork(s, e)
			}, n)
			for _, err := range errs {
				if err != nil {
					return err
				}
			}
		}

		nextAffected = nextAffected[:0]
		for i := 0; i < n; i++ {
			if parentOut[i] != ^uint64(0) {
				nextAffected = append(nextAffected, parentOut[i])
			}
		}
		slices.SortFunc(nextAffected, func(a, b uint64) bool { return a < b })
		j = 0
		for i := 0; i < len(nextAffected); i++ {
			if i == 0 || nextAffected[i] != nextAffected[i-1] {
				nextAffected[j] = nextAffected[i]
				j++
			}
		}
		nextAffected = nextAffected[:j]
		affected, nextAffected = nextAffected, affected
	}

	return nil
}

func (f *Forest) collectRoots(snap *ForestView, numLeaves uint64) ([]Hash, uint64, error) {
	rootPositions := RootPositions(numLeaves, f.forestRows)
	roots := make([]Hash, len(rootPositions))
	for i, pos := range rootPositions {
		if snap.bitmap.isSet(pos) {
			roots[i] = empty
			continue
		}
		hash, err := f.readHashAt(pos)
		if err != nil {
			return nil, 0, fmt.Errorf("read root at position %d: %w", pos, err)
		}
		roots[i] = hash
	}

	return roots, numLeaves, nil
}

// readHashAt reads the hash at the given position. Uses the value-typed
// HashAt to keep the result on the caller's stack frame; routing through
// io.ReaderAt forces the buffer to escape to the heap.
func (f *Forest) readHashAt(position uint64) (Hash, error) {
	return f.file.HashAt(f.posToFileOffset(position))
}

// writeHashAt writes the hash at the given position. Uses the value-typed
// PutHashAt to avoid the heap allocation that an io.WriterAt-typed slice
// would force on the caller.
func (f *Forest) writeHashAt(position uint64, hash Hash) error {
	return f.file.PutHashAt(hash, f.posToFileOffset(position))
}
