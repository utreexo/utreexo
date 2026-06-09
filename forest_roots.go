package utreexo

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
