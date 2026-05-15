package utreexo

import (
	"runtime"
	"sync"
)

// minParallelSize is the minimum number of work items before the code uses
// the worker pools. Below this threshold, launch/sync overhead dominates.
const minParallelSize = 4096

// numWorkers is the number of goroutines used by the persistent worker pools.
var numWorkers = runtime.NumCPU()

// workerPool is a persistent pool of goroutines. Each worker has its own Cond
// variable. Only workers with actual work are signaled, and only active workers
// are counted in the WaitGroup. Idle workers stay parked.
type workerPool struct {
	n       int
	workers []poolWorker
	wg      sync.WaitGroup
}

type poolWorker struct {
	mu    sync.Mutex
	cond  *sync.Cond
	gen   uint64
	fn    func(wIdx, start, end int)
	start int
	end   int
}

func newWorkerPool(n int) *workerPool {
	p := &workerPool{
		n:       n,
		workers: make([]poolWorker, n),
	}
	for i := 0; i < n; i++ {
		p.workers[i].cond = sync.NewCond(&p.workers[i].mu)
		go p.worker(i)
	}
	return p
}

func (p *workerPool) worker(idx int) {
	w := &p.workers[idx]
	var lastGen uint64
	w.mu.Lock()
	for {
		for w.gen == lastGen {
			w.cond.Wait()
		}
		lastGen = w.gen
		fn := w.fn
		start, end := w.start, w.end
		w.mu.Unlock()

		fn(idx, start, end)
		p.wg.Done()

		w.mu.Lock()
	}
}

func (p *workerPool) do(fn func(wIdx, start, end int), n int) {
	if n <= 0 {
		return
	}

	workers := p.n
	if workers > n {
		workers = n
	}
	chunkSize := (n + workers - 1) / workers

	active := 0
	for i := 0; i < workers; i++ {
		start := i * chunkSize
		end := start + chunkSize
		if end > n {
			end = n
		}
		if start >= end {
			break
		}
		active++
	}

	p.wg.Add(active)

	for i := 0; i < active; i++ {
		w := &p.workers[i]
		w.mu.Lock()
		w.fn = fn
		w.start = i * chunkSize
		w.end = w.start + chunkSize
		if w.end > n {
			w.end = n
		}
		w.gen++
		w.mu.Unlock()
		w.cond.Signal()
	}

	p.wg.Wait()
}

// mainPool is used by the main thread (Record, parallelLeafHash).
var mainPool = newWorkerPool(numWorkers)

// pipelinePool is used by the pipeline goroutine (GenerateRootsAndProof).
var pipelinePool = newWorkerPool(numWorkers)

// MainParallelDo splits n work items across the main thread's persistent pool
// workers.
func MainParallelDo(fn func(wIdx, start, end int), n int) {
	mainPool.do(fn, n)
}

// pipelineParallelDo splits n work items across persistent pipeline workers.
func pipelineParallelDo(fn func(wIdx, start, end int), n int) {
	pipelinePool.do(fn, n)
}
