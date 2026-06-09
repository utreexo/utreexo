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
	numWorkers int
	workers    []poolWorker
	wg         sync.WaitGroup
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
		numWorkers: n,
		workers:    make([]poolWorker, n),
	}
	for i := 0; i < n; i++ {
		p.workers[i].cond = sync.NewCond(&p.workers[i].mu)
		go p.worker(i)
	}
	return p
}

// worker runs one pool goroutine for the lifetime of the pool: it parks until
// do() hands it a job, runs that job, reports done, and parks again.
func (p *workerPool) worker(idx int) {
	w := &p.workers[idx]

	// lastGen is the job number this worker has already run. do() bumps w.gen to
	// publish a new job, so w.gen != lastGen means a job is waiting.
	var lastGen uint64

	w.mu.Lock()
	for {
		// Sleep until do() publishes a new job. cond.Wait() releases w.mu while
		// parked and re-acquires it on wake. The predicate is a for-loop, not an
		// if, to re-check after waking as a condition variable requires.
		for w.gen == lastGen {
			w.cond.Wait()
		}

		// Snapshot the job under the lock so the work below can run without it.
		lastGen = w.gen
		fn := w.fn
		start, end := w.start, w.end
		w.mu.Unlock()

		// Run the assigned slice with no lock held, then report completion;
		// do()'s wg.Wait() returns once every worker has called Done().
		fn(idx, start, end)
		p.wg.Done()

		w.mu.Lock()
	}
}

// do splits n work items (indexed 0..n-1) across the pool's workers and blocks
// until all of them finish. Only one goroutine may call do() on a given pool at
// a time; each package-level pool is driven by a single caller.
func (p *workerPool) do(fn func(wIdx, start, end int), n int) {
	// Nothing to do. Also avoids a divide-by-zero below: with n == 0, workers
	// would be 0.
	if n <= 0 {
		return
	}

	// Crew size: one worker per item, but never more than the pool has. Capping
	// at n guarantees every worker below gets a non-empty range.
	workers := p.numWorkers
	if workers > n {
		workers = n
	}

	// Arm the barrier for every worker; each runs one chunk and calls Done() once.
	p.wg.Add(workers)

	// Hand each worker its slice and wake it. This pairs with worker(): what gets
	// written here under the lock is what the worker reads.
	for i := 0; i < workers; i++ {
		w := &p.workers[i]

		// Hold the worker's lock only for the handoff. gen is the new-job signal
		// the worker watches; bumping it while locked means the worker never sees
		// a half-written job (gen changed but start/end stale).
		w.mu.Lock()
		w.fn = fn
		// Worker i takes [i*n/workers, (i+1)*n/workers); these contiguous ranges
		// cover [0,n) exactly once, with sizes differing by at most one item.
		w.start = i * n / workers
		w.end = (i + 1) * n / workers
		w.gen++
		w.mu.Unlock()

		// Wake the worker if it's parked in cond.Wait(). Signaled after the unlock
		// so it doesn't wake into a lock still held here. If it isn't parked yet,
		// the signal is dropped harmlessly: gen already changed, so the worker's
		// next check catches the job anyway.
		w.cond.Signal()
	}

	// Block until every worker has finished its chunk. On return all n items are
	// processed and the counter is back at 0 for the next call.
	p.wg.Wait()
}

// mainPool is used by the main thread for positionMap Get fan-out in Record.
var mainPool = newWorkerPool(numWorkers)

// recordBgPool serves Record's hash-write fan-out so it can run concurrently
// with the positionMap Get fan-out on mainPool.
var recordBgPool = newWorkerPool(numWorkers)

// pipelinePool runs the per-row rehash work dispatched by runRowWork.
var pipelinePool = newWorkerPool(numWorkers)

// MainParallelDo splits n work items across the main thread's persistent pool
// workers.
func MainParallelDo(fn func(wIdx, start, end int), n int) {
	mainPool.do(fn, n)
}

// recordBgParallelDo splits n work items across the record background pool.
func recordBgParallelDo(fn func(wIdx, start, end int), n int) {
	recordBgPool.do(fn, n)
}

// pipelineParallelDo splits n work items across persistent pipeline workers.
func pipelineParallelDo(fn func(wIdx, start, end int), n int) {
	pipelinePool.do(fn, n)
}
