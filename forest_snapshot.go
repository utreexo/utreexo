package utreexo

// bitmapSnapshot provides a read-only, immutable view of the bitmap at
// snapshot time. It owns a private copy of the bits slice, so the writer can
// freely mutate the live bitmap without locks or COW overhead.
type bitmapSnapshot struct {
	bits []uint64 // private copy made at snapshot time; never modified
}

// isSet returns true if pos was marked as deleted at snapshot time.
func (s *bitmapSnapshot) isSet(pos uint64) bool {
	word := pos / 64
	if word >= uint64(len(s.bits)) {
		return false
	}
	return s.bits[word]&(1<<(pos%64)) != 0
}

// bitmapBufCh is a channel-based pool for snapshot buffers. Unlike sync.Pool,
// items in a buffered channel survive GC cycles, avoiding allocation churn when
// GC is already under pressure.
var bitmapBufCh = make(chan []uint64, 64)

// snapshot creates an immutable copy of the current bitmap state.
func (b *deletedBitmap) snapshot() *bitmapSnapshot {
	needed := len(b.bits)
	var buf []uint64
	select {
	case buf = <-bitmapBufCh:
		if cap(buf) < needed {
			buf = make([]uint64, needed)
		} else {
			buf = buf[:needed]
		}
	default:
		buf = make([]uint64, needed)
	}
	copy(buf, b.bits)
	return &bitmapSnapshot{bits: buf}
}

// ForestView is an immutable view of the forest state at a point in time.
// It captures numLeaves and a bitmap snapshot so concurrent readers can compute
// roots and proofs while the writer continues calling Record.
type ForestView struct {
	numLeaves   uint64
	bitmap      *bitmapSnapshot
	pendingDels []uint64 // leaf positions deleted since last snapshot
}

// Snapshot captures the current forest state for concurrent root/proof generation.
// Only one snapshot may be active at a time. Call ReleaseSnapshot when done.
func (f *Forest) Snapshot() *ForestView {
	f.mu.Lock()
	defer f.mu.Unlock()
	snap := &ForestView{
		numLeaves:   f.NumLeaves,
		bitmap:      f.deletedLeafPositions.snapshot(),
		pendingDels: f.pendingDels,
	}
	f.pendingDels = nil
	return snap
}

// ReleaseSnapshot returns the snapshot's bitmap buffer to the channel pool for
// reuse, reducing GC pressure from per-block bitmap copies.
func (f *Forest) ReleaseSnapshot(snap *ForestView) {
	if snap == nil || snap.bitmap == nil || snap.bitmap.bits == nil {
		return
	}
	select {
	case bitmapBufCh <- snap.bitmap.bits:
	default:
		// Channel full; let GC collect this buffer.
	}
	snap.bitmap.bits = nil
}
