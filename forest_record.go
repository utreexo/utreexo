package utreexo

import "fmt"

// Record adds and deletes elements without computing parent hashes.
// Use during IBD for performance; call HashAll or GenerateRootsAndProof when
// done to build the tree. It returns add indexes and leaf positions for deleted
// leaves.
func (f *Forest) Record(adds []Hash, delHashes []Hash) ([]int32, []uint64, error) {
	f.mu.Lock()
	defer f.mu.Unlock()

	type delResult struct {
		addIndex int32
		leafPos  uint64
	}
	delResults := make([]delResult, len(delHashes))

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
				delResults[i] = delResult{unpackIndex(packed), unpackPos(packed)}
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
					delResults[i] = delResult{unpackIndex(packed), unpackPos(packed)}
				}
			}, nDels)
			for _, err := range errs {
				if err != nil {
					return nil, nil, err
				}
			}
		}
	}

	addIndexes := make([]int32, len(delHashes))
	delPositions := make([]uint64, len(delHashes))
	for i, dr := range delResults {
		addIndexes[i] = dr.addIndex
		delPositions[i] = dr.leafPos
		f.deletedLeafPositions.set(dr.leafPos)
		f.pendingDels = append(f.pendingDels, dr.leafPos)
	}

	startPos := f.NumLeaves
	if len(adds) > 0 {
		batch, err := f.positionMap.BeginBatch(uint64(len(adds)))
		if err != nil {
			return nil, nil, fmt.Errorf("positionMap.BeginBatch: %w", err)
		}
		for i, hash := range adds {
			offset := f.posToFileOffset(startPos + uint64(i))
			if err := f.file.PutHashAt(hash, offset); err != nil {
				return nil, nil, fmt.Errorf("write leaf %d: %w", i, err)
			}
			if hash != empty {
				if err := batch.Insert(hash, packPosIndex(startPos+uint64(i), int32(i))); err != nil {
					return nil, nil, fmt.Errorf("positionMap.Insert: %w", err)
				}
			}
		}
	}
	f.NumLeaves += uint64(len(adds))

	if err := f.appendBlockCount(uint32(len(adds))); err != nil {
		return nil, nil, fmt.Errorf("append block count: %w", err)
	}

	f.recordMode = true
	if err := f.saveMetadata(); err != nil {
		return nil, nil, fmt.Errorf("save metadata: %w", err)
	}
	return addIndexes, delPositions, nil
}

// ExitRecordMode transitions the forest out of record mode after
// GenerateRootsAndProof has written all intermediate hashes to the data file.
func (f *Forest) ExitRecordMode() error {
	f.mu.Lock()
	defer f.mu.Unlock()

	if !f.recordMode {
		return nil
	}

	f.recordMode = false
	if err := f.saveMetadata(); err != nil {
		return fmt.Errorf("save metadata: %w", err)
	}
	return nil
}

// IsRecordMode returns true if the forest is in record mode.
func (f *Forest) IsRecordMode() bool {
	f.mu.RLock()
	defer f.mu.RUnlock()
	return f.recordMode
}
