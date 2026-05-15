package utreexo

import (
	"fmt"

	"golang.org/x/exp/slices"
)

// GenerateRootsAndProof computes the roots and the inclusion proof for
// snap.pendingDels in a single pass. The sibling hashes that the rehash walk
// reads to compute deletion-path parents are exactly the proof hashes, so the
// proof comes "for free" off the rehash without a second walk over the file.
//
// Internally adds run first, then the rehash-with-proof pass. This ordering
// ensures that when rehash reads a sibling on the add path (e.g. a parent of
// newly appended leaves), the value is already in the file. The intermediate
// values that adds writes for positions later overwritten by rehash do not
// affect the final roots — adds and rehash both write the same final value
// for any shared position.
func (f *Forest) GenerateRootsAndProof(snap *ForestView) ([]Hash, uint64, Proof, error) {
	totalLeaves := snap.numLeaves
	forestRows := f.forestRows
	prevLeaves := f.lastGeneratedLeaves.Load()

	fromLeaves := prevLeaves
	if prevLeaves == 0 || prevLeaves > totalLeaves {
		fromLeaves = 0
	}
	if err := f.processAddsParallel(snap, fromLeaves, totalLeaves, forestRows); err != nil {
		return nil, 0, Proof{}, err
	}

	proof, err := f.rehashDeletionsAndCaptureProof(snap, totalLeaves, forestRows)
	if err != nil {
		return nil, 0, Proof{}, err
	}

	f.lastGeneratedLeaves.Store(totalLeaves)
	roots, numLeaves, err := f.collectRoots(snap, totalLeaves)
	if err != nil {
		return nil, 0, Proof{}, err
	}

	return roots, numLeaves, proof, nil
}

// rehashDeletionsAndCaptureProof rehashes the deletion paths and assembles the
// inclusion proof for snap.pendingDels. At each row, every "lone" entry (one
// whose sibling is not also affected, i.e. not de-twinned) has a sibling whose
// hash is already being read for the parent computation — that read is the
// proof hash for that row.
//
// The returned Proof's Targets are snap.pendingDels sorted ascending (and
// translated to defaultForestRows when forestRows differs). Proof hashes are
// in (row ascending, sorted position within row) order, matching the layout
// calculateHashes expects.
func (f *Forest) rehashDeletionsAndCaptureProof(snap *ForestView, numLeaves uint64, forestRows uint8) (Proof, error) {
	if len(snap.pendingDels) == 0 {
		return Proof{}, nil
	}

	affected := make([]uint64, len(snap.pendingDels))
	copy(affected, snap.pendingDels)
	slices.SortFunc(affected, func(a, b uint64) bool { return a < b })

	targets := make([]uint64, len(affected))
	copy(targets, affected)
	if forestRows != defaultForestRows {
		targets = translatePositions(targets, forestRows, defaultForestRows)
	}

	isLone := make([]bool, len(affected))
	for i := range isLone {
		isLone[i] = true
	}

	parentOut := make([]uint64, len(affected))
	proofSlots := make([]Hash, len(affected))
	hasProof := make([]bool, len(affected))
	nextAffected := make([]uint64, 0, len(affected))
	nextIsLone := make([]bool, 0, len(affected))
	errs := make([]error, numWorkers)

	// Pre-size proofHashes to len(pendingDels) so the per-row append from
	// a nil start doesn't trigger the usual growth chain. The bound holds
	// in practice — most deletion paths contribute one lone-sibling proof
	// hash each, and de-twinned pairs contribute none.
	proofHashes := make([]Hash, 0, len(snap.pendingDels))

	for row := uint8(0); row < forestRows && len(affected) > 0; row++ {
		n := len(affected)

		for i := 0; i < n-1; i++ {
			if affected[i] == ^uint64(0) {
				continue
			}
			if affected[i]^1 == affected[i+1] {
				affected[i] = leftSib(affected[i])
				isLone[i] = false
				affected[i+1] = ^uint64(0)
			}
		}

		j := 0
		for i := 0; i < n; i++ {
			if affected[i] != ^uint64(0) {
				affected[j] = affected[i]
				isLone[j] = isLone[i]
				j++
			}
		}
		affected = affected[:j]
		isLone = isLone[:j]
		n = j

		if n == 0 {
			break
		}

		if cap(parentOut) < n {
			parentOut = make([]uint64, n)
			proofSlots = make([]Hash, n)
			hasProof = make([]bool, n)
		}
		parentOut = parentOut[:n]
		proofSlots = proofSlots[:n]
		hasProof = hasProof[:n]
		for i := 0; i < n; i++ {
			hasProof[i] = false
		}

		rehashWork := func(s, e int) error {
			for i := s; i < e; i++ {
				pos := affected[i]

				if isRootPositionTotalRows(pos, numLeaves, forestRows) {
					if row == 0 {
						_ = f.writeHashAt(pos, empty)
					}
					parentOut[i] = ^uint64(0)
					continue
				}

				currentHash, err := f.readHashForProof(pos, snap)
				if err != nil {
					currentHash = empty
				}

				sibPos := sibling(pos)
				sibHash, err := f.readHashForProof(sibPos, snap)
				if err != nil {
					sibHash = empty
				}

				if isLone[i] {
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
				parentOut[i] = parentPos
			}
			return nil
		}

		if n < minParallelSize {
			if err := rehashWork(0, n); err != nil {
				return Proof{}, err
			}
		} else {
			for i := range errs {
				errs[i] = nil
			}
			pipelineParallelDo(func(wIdx, s, e int) {
				errs[wIdx] = rehashWork(s, e)
			}, n)
			for _, err := range errs {
				if err != nil {
					return Proof{}, err
				}
			}
		}

		for i := 0; i < n; i++ {
			if hasProof[i] {
				proofHashes = append(proofHashes, proofSlots[i])
			}
		}

		nextAffected = nextAffected[:0]
		nextIsLone = nextIsLone[:0]
		for i := 0; i < n; i++ {
			if parentOut[i] != ^uint64(0) {
				nextAffected = append(nextAffected, parentOut[i])
				nextIsLone = append(nextIsLone, true)
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
		nextIsLone = nextIsLone[:j]

		affected, nextAffected = nextAffected, affected
		isLone, nextIsLone = nextIsLone, isLone
	}

	return Proof{Targets: targets, Proof: proofHashes}, nil
}

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
