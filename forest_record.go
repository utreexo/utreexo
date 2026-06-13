package utreexo

import (
	"fmt"
	"sync"
)

// Record adds and deletes elements without computing parent hashes. The forest
// must be in record mode first (see EnterRecordMode); Record errors otherwise.
// Use during IBD for performance; call RehashAndProve per block, or HashAll
// when done, to build the tree. It returns add indexes and leaf positions for
// deleted leaves.
func (f *Forest) Record(adds []Hash, delHashes []Hash) ([]int32, []uint64, error) {
	f.mu.Lock()
	defer f.mu.Unlock()

	if !f.recordMode {
		return nil, nil, fmt.Errorf("cannot call Record outside record mode; call EnterRecordMode first")
	}

	// Record appends leaves and marks deletions without building their parent
	// hashes, so the persisted generated-leaves slot can no longer claim the
	// tree is complete. Zero the slot but not lastGeneratedLeaves: the next
	// RehashAndProve still resumes incrementally, while a crash reopens to a
	// full rebuild. A call that records nothing leaves the slot alone.
	if len(adds) > 0 || len(delHashes) > 0 {
		if err := f.clearGeneratedLeaves(); err != nil {
			return nil, nil, fmt.Errorf("clear generated leaves: %w", err)
		}
	}

	// writeAddHashes runs in a background goroutine: the file offsets it
	// writes are disjoint from positionMap and deletedLeafPositions, so it
	// overlaps freely with processDeletions and the batch.Insert loop.
	// Get-before-Insert ordering on positionMap is preserved by running
	// processDeletions before the Insert loop on the main goroutine.
	startPos := f.NumLeaves
	var hashErr error
	var hashWg sync.WaitGroup
	if len(adds) > 0 {
		hashWg.Add(1)
		go func() {
			defer hashWg.Done()
			hashErr = f.writeAddHashes(adds, startPos)
		}()
	}

	addIndexes, delPositions, err := f.processDeletions(delHashes)
	if err != nil {
		hashWg.Wait()
		return nil, nil, err
	}
	f.unmaskedDels += uint64(len(delPositions))

	if len(adds) > 0 {
		batch, err := f.positionMap.BeginBatch(uint64(len(adds)))
		if err != nil {
			hashWg.Wait()
			return nil, nil, fmt.Errorf("positionMap.BeginBatch: %w", err)
		}
		for i, hash := range adds {
			if hash != empty {
				if err := batch.Insert(hash, packPosIndex(startPos+uint64(i), int32(i))); err != nil {
					hashWg.Wait()
					return nil, nil, fmt.Errorf("positionMap.Insert: %w", err)
				}
			}
		}
	}

	hashWg.Wait()
	if hashErr != nil {
		return nil, nil, hashErr
	}
	f.NumLeaves += uint64(len(adds))

	if err := f.appendBlockCount(uint32(len(adds))); err != nil {
		return nil, nil, fmt.Errorf("append block count: %w", err)
	}

	if err := f.saveNumLeaves(); err != nil {
		return nil, nil, fmt.Errorf("save num leaves: %w", err)
	}
	return addIndexes, delPositions, nil
}

// processDeletions looks up each delHash in positionMap to produce its addIndex
// and leaf position, then marks each position in the deletedLeafPositions
// bitmap. The Get fan-out runs in parallel above minParallelSize; the bitmap
// updates are serial since deletedBitmap.set is not concurrency-safe.
func (f *Forest) processDeletions(delHashes []Hash) ([]int32, []uint64, error) {
	addIndexes := make([]int32, len(delHashes))
	delPositions := make([]uint64, len(delHashes))

	if nDels := len(delHashes); nDels > 0 {
		if nDels < minParallelSize {
			for i, delHash := range delHashes {
				packed, found, err := f.positionMap.Get(delHash)
				if err != nil {
					return nil, nil, fmt.Errorf("positionMap.Get: %w", err)
				}
				if !found {
					return nil, nil, fmt.Errorf("delhash %v not found in position map", delHash)
				}
				addIndexes[i] = unpackIndex(packed)
				delPositions[i] = unpackPos(packed)
			}
		} else {
			errs := make([]error, numWorkers)
			MainParallelDo(func(wIdx, s, e int) {
				for i := s; i < e; i++ {
					packed, found, err := f.positionMap.Get(delHashes[i])
					if err != nil {
						errs[wIdx] = fmt.Errorf("positionMap.Get: %w", err)
						return
					}
					if !found {
						errs[wIdx] = fmt.Errorf("delhash %v not found in position map", delHashes[i])
						return
					}
					addIndexes[i] = unpackIndex(packed)
					delPositions[i] = unpackPos(packed)
				}
			}, nDels)
			for _, err := range errs {
				if err != nil {
					return nil, nil, err
				}
			}
		}
	}

	for _, pos := range delPositions {
		f.deletedLeafPositions.set(pos)
	}
	return addIndexes, delPositions, nil
}

// writeAddHashes writes each add to the mmap file at startPos+i. The writes
// touch disjoint offsets and are fanned out across recordBgPool above
// minParallelSize so the loop can overlap with positionMap work on mainPool.
func (f *Forest) writeAddHashes(adds []Hash, startPos uint64) error {
	if len(adds) == 0 {
		return nil
	}
	if len(adds) < minParallelSize {
		for i, hash := range adds {
			offset := f.posToFileOffset(startPos + uint64(i))
			if err := f.file.PutHashAt(hash, offset); err != nil {
				return fmt.Errorf("write leaf %d: %w", i, err)
			}
		}
		return nil
	}
	errs := make([]error, numWorkers)
	recordBgParallelDo(func(wIdx, s, e int) {
		for i := s; i < e; i++ {
			offset := f.posToFileOffset(startPos + uint64(i))
			if err := f.file.PutHashAt(adds[i], offset); err != nil {
				errs[wIdx] = fmt.Errorf("write leaf %d: %w", i, err)
				return
			}
		}
	}, len(adds))
	for _, err := range errs {
		if err != nil {
			return err
		}
	}
	return nil
}

// EnterRecordMode transitions the forest into record mode, the deferred-hashing
// state in which Record runs. The normal mutation paths (Modify, Undo,
// ModifyAndReturnTTLs) refuse to run until HashAll or ExitRecordMode returns the
// forest to normal mode.
func (f *Forest) EnterRecordMode() error {
	f.mu.Lock()
	defer f.mu.Unlock()

	if f.recordMode {
		return nil
	}

	f.recordMode = true
	if err := f.saveRecordMode(); err != nil {
		return fmt.Errorf("save record mode: %w", err)
	}
	return nil
}

// ExitRecordMode transitions the forest out of record mode after GenerateRoots
// has written all intermediate hashes to the data file.
func (f *Forest) ExitRecordMode() error {
	f.mu.Lock()
	defer f.mu.Unlock()

	if !f.recordMode {
		return nil
	}

	f.recordMode = false
	if err := f.saveRecordMode(); err != nil {
		return fmt.Errorf("save record mode: %w", err)
	}
	return nil
}

// IsRecordMode returns true if the forest is in record mode.
func (f *Forest) IsRecordMode() bool {
	f.mu.RLock()
	defer f.mu.RUnlock()
	return f.recordMode
}
