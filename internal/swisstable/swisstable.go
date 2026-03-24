//go:build unix

package swisstable

// SwissPositionMap is a disk-backed hash table using the Swiss Table algorithm.
//
// Design:
//   - Maps 32-byte hashes to 8-byte packed positions
//   - Uses mmap'd files for persistence (ctrl bytes + slots)
//   - Hashes are NOT stored in the table; lookups verify by reading from dataFile
//   - Automatically resizes (doubles) when full
//
// Memory layout:
//   - ctrl file: 1 byte per slot (control byte)
//   - slots file: 8 bytes per slot (packed position)
//   - Total: 9 bytes per slot, ~13 bytes per entry at 70% load
//
// Control byte encoding:
//   - 0b00000000: empty slot
//   - 0b01111111: deleted slot (tombstone)
//   - 0b1xxxxxxx: full slot, lower 7 bits are H2 (secondary hash)

import (
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"math/bits"
	"os"
	"slices"
	"syscall"
)

// Control byte constants.
const (
	groupSize   = 16         // slots per group (SIMD register width)
	ctrlEmpty   = 0b00000000 // empty slot
	ctrlDeleted = 0b01111111 // deleted slot (tombstone)
	ctrlFull    = 0b10000000 // high bit set = full, lower 7 bits = H2

	// fileHeaderSize is the size of the header in ctrl and slots files (stores consistency hash)
	fileHeaderSize = 32 // 32-byte hash for consistency check with WAL
)

// SwissPositionMap is a Swiss Table mapping hashes to positions.
//
// It is NOT safe for concurrent use. Callers must synchronize access
// when multiple goroutines may call Get, Set, or Delete concurrently.
// Concurrent read-only access (Get) is safe when no overlay entries exist.
type SwissPositionMap struct {
	// Mmap'd data
	ctrlMmap  []byte // full mmap including header
	ctrl      []byte // control bytes (1 per slot), points into ctrlMmap after header
	slotsMmap []byte // full mmap including header
	slots     []byte // packed positions (8 bytes per slot), points into slotsMmap after header

	// File handles for mmap
	ctrlFile  *os.File
	slotsFile *os.File

	// Table sizing
	numSlots  uint64
	numGroups uint64 // numSlots / groupSize

	// For hash verification (we don't store hashes, we verify from source)
	dataFile io.ReaderAt
	posMask  uint64 // mask to extract position from packed value

	// Entry count
	count uint64

	// Write overlay: pending changes not yet flushed to disk.
	// During normal operation, Set/Delete write here instead of the mmap.
	// On flush, the WAL journals these entries and applies them to the
	// underlying files via fd writes. The mmap (MAP_SHARED) then reflects
	// the new data through the shared page cache.
	ctrlOverlay  map[uint64]byte
	slotsOverlay map[uint64]uint64
	dirtyGroups  map[uint64]struct{} // groups with overlay entries (fast path)
	baseCount    uint64              // count from on-disk/mmap state (for DiscardPending)
}

// ----------------------------------------------------------------------------
// Constructor
// ----------------------------------------------------------------------------

// NewSwissPositionMap creates a new Swiss Table backed by mmap'd files.
// Returns the map and a bool indicating if rebuild is needed (consistency hash mismatch).
// Pass a zero hash to force rebuild. posMask is applied to packed values to
// extract the leaf position for hash verification against dataFile.
// The caller must open ctrlFile and slotsFile before calling this function;
// the SwissPositionMap takes ownership and will close them in Close().
func NewSwissPositionMap(ctrlFile, slotsFile *os.File, expectedEntries uint64, consistencyHash [32]byte, dataFile io.ReaderAt, posMask uint64) (*SwissPositionMap, bool, error) {
	if dataFile == nil {
		return nil, false, fmt.Errorf("dataFile must not be nil")
	}

	ctrlMmap, slotsBytes, numSlots, needsRebuild, err := openFiles(ctrlFile, slotsFile, expectedEntries, consistencyHash)
	if err != nil {
		return nil, false, err
	}

	// ctrl and slot bytes start after header
	ctrl := ctrlMmap[fileHeaderSize:]
	slots := slotsBytes[fileHeaderSize:]

	var count uint64
	// Restore count from existing data if not rebuilding
	if !needsRebuild {
		for _, c := range ctrl {
			if c&ctrlFull != 0 {
				count++
			}
		}
	}

	m := &SwissPositionMap{
		ctrlMmap:     ctrlMmap,
		ctrl:         ctrl,
		slotsMmap:    slotsBytes,
		slots:        slots,
		ctrlFile:     ctrlFile,
		slotsFile:    slotsFile,
		numSlots:     numSlots,
		numGroups:    numSlots / groupSize,
		dataFile:     dataFile,
		posMask:      posMask,
		count:        count,
		ctrlOverlay:  make(map[uint64]byte),
		slotsOverlay: make(map[uint64]uint64),
		dirtyGroups:  make(map[uint64]struct{}),
		baseCount:    count,
	}

	return m, needsRebuild, nil
}

// openFiles mmaps the ctrl and slots files, wiping both if either
// are inconsistent. Returns the actual numSlots and needsRebuild=true if files
// were wiped (hash mismatch, size mismatch, or zero consistency hash).
// expectedEntries is only used to size new files when rebuilding; consistent
// files are reused at their on-disk size regardless of expectedEntries.
// The caller must open the files before calling this function.
func openFiles(ctrlFile, slotsFile *os.File, expectedEntries uint64, consistencyHash [32]byte) (
	ctrlMmap, slotsBytes []byte, numSlots uint64, needsRebuild bool, err error) {

	ctrlFi, err := ctrlFile.Stat()
	if err != nil {
		return nil, nil, 0, false, err
	}
	slotsFi, err := slotsFile.Stat()
	if err != nil {
		return nil, nil, 0, false, err
	}

	needsRebuild = true

	// Check whether existing files are consistent: the consistency hash must
	// be non-zero, stored hashes must match, and ctrl/slots file sizes must
	// agree on the same valid number of slots.
	var ctrlHash, slotsHash [32]byte
	ctrlFile.ReadAt(ctrlHash[:], 0)
	slotsFile.ReadAt(slotsHash[:], 0)
	if consistencyHash != [32]byte{} &&
		ctrlHash == consistencyHash &&
		slotsHash == consistencyHash {
		// Hashes match. Derive numSlots from actual file sizes and verify
		// that ctrl and slots are self-consistent. This allows reusing
		// files that grew via resize() even if expectedEntries changed.
		fileNumSlots := uint64(ctrlFi.Size()) - fileHeaderSize
		if fileNumSlots > 0 &&
			fileNumSlots%groupSize == 0 &&
			slotsFi.Size() == int64(fileHeaderSize+fileNumSlots*8) {
			numSlots = fileNumSlots
			needsRebuild = false
		}
	}

	// If rebuild needed, compute numSlots from expectedEntries and wipe both
	// files so the OS provides fresh zero-filled pages.
	if needsRebuild {
		numSlots = max(roundUpGroupSize(expectedEntries*10/7), groupSize)
		ctrlSize := int64(fileHeaderSize + numSlots)
		slotsSize := int64(fileHeaderSize + numSlots*8)
		for _, wipe := range []struct {
			f    *os.File
			size int64
			name string
		}{
			{ctrlFile, ctrlSize, "ctrl"},
			{slotsFile, slotsSize, "slots"},
		} {
			if err := wipe.f.Truncate(0); err != nil {
				return nil, nil, 0, false, fmt.Errorf("truncate %s: %w", wipe.name, err)
			}
			if err := wipe.f.Truncate(wipe.size); err != nil {
				return nil, nil, 0, false, fmt.Errorf("extend %s: %w", wipe.name, err)
			}
		}
	}

	// Mmap both files.
	ctrlSize := int64(fileHeaderSize + numSlots)
	slotsSize := int64(fileHeaderSize + numSlots*8)
	ctrlMmap, err = syscall.Mmap(int(ctrlFile.Fd()), 0, int(ctrlSize),
		syscall.PROT_READ|syscall.PROT_WRITE, mmapFlags)
	if err != nil {
		return nil, nil, 0, false, fmt.Errorf("mmap ctrl: %w", err)
	}
	slotsBytes, err = syscall.Mmap(int(slotsFile.Fd()), 0, int(slotsSize),
		syscall.PROT_READ|syscall.PROT_WRITE, mmapFlags)
	if err != nil {
		syscall.Munmap(ctrlMmap)
		return nil, nil, 0, false, fmt.Errorf("mmap slots: %w", err)
	}

	return ctrlMmap, slotsBytes, numSlots, needsRebuild, nil
}

// roundUpGroupSize rounds n up to the nearest multiple of groupSize.
func roundUpGroupSize(n uint64) uint64 {
	return ((n + groupSize - 1) / groupSize) * groupSize
}

// ----------------------------------------------------------------------------
// Public API
// ----------------------------------------------------------------------------

// Get looks up a hash and returns its packed position.
func (m *SwissPositionMap) Get(hash [32]byte) (uint64, bool, error) {
	h1, h2 := splitHash(hash)
	start := h1 % m.numGroups

	var groupBuf [groupSize]byte
	for i := range m.numGroups {
		base := m.groupBase(start, i)
		group := m.loadGroupCtrl(base, &groupBuf)

		// Check slots with matching H2
		for matches := matchH2(group, h2); matches != 0; matches &= matches - 1 {
			slot := base + uint64(bits.TrailingZeros16(matches))
			packed := m.getSlot(slot)
			ok, err := m.verifyHash(packed, hash)
			if err != nil {
				return 0, false, fmt.Errorf("swiss get: %w", err)
			}
			if ok {
				return packed, true, nil
			}
		}

		// Empty slot means key doesn't exist
		if matchEmpty(group) != 0 {
			return 0, false, nil
		}
	}
	return 0, false, nil
}

// Set stores a hash -> packed position mapping, resizing the table if needed.
func (m *SwissPositionMap) Set(hash [32]byte, packed uint64) error {
	// Resize before inserting if load factor would exceed 70%.
	if (m.count+1)*10 > m.numSlots*7 {
		if err := m.resize(); err != nil {
			return err
		}
	}

	return m.set(hash, packed)
}

// set inserts or updates a hash -> packed position mapping without checking
// the load factor.
func (m *SwissPositionMap) set(hash [32]byte, packed uint64) error {
	h1, h2 := splitHash(hash)
	start := h1 % m.numGroups

	// Track first available slot for insertion. We must complete the full
	// probe sequence (stopping only at empty, not deleted) to avoid inserting
	// a duplicate when the key exists in a later group.
	firstAvail := uint64(0)
	hasAvail := false

	var groupBuf [groupSize]byte
	for i := range m.numGroups {
		base := m.groupBase(start, i)
		group := m.loadGroupCtrl(base, &groupBuf)

		// Check if key exists (update in place)
		for matches := matchH2(group, h2); matches != 0; matches &= matches - 1 {
			slot := base + uint64(bits.TrailingZeros16(matches))
			ok, err := m.verifyHash(m.getSlot(slot), hash)
			if err != nil {
				return fmt.Errorf("swiss set: %w", err)
			}
			if ok {
				m.setSlot(slot, packed)
				return nil
			}
		}

		// Remember first available slot, but don't insert yet
		if !hasAvail {
			if avail := matchEmptyOrDeleted(group); avail != 0 {
				firstAvail = base + uint64(bits.TrailingZeros16(avail))
				hasAvail = true
			}
		}

		// Empty slot means the key definitely doesn't exist further
		if matchEmpty(group) != 0 {
			break
		}
	}

	if !hasAvail {
		return fmt.Errorf("swiss table: no available slot (count=%d, slots=%d)", m.count, m.numSlots)
	}

	m.setCtrl(firstAvail, h2)
	m.setSlot(firstAvail, packed)
	m.count++
	return nil
}

// Delete removes a hash from the table.
//
// Note: Delete leaves a tombstone (ctrlDeleted) which can degrade probe
// performance if tombstones accumulate without a resize to clear them.
// In practice this is not a concern because Delete is only called during
// Undo (block disconnects), which is rare.
func (m *SwissPositionMap) Delete(hash [32]byte) (bool, error) {
	h1, h2 := splitHash(hash)
	start := h1 % m.numGroups

	var groupBuf [groupSize]byte
	for i := range m.numGroups {
		base := m.groupBase(start, i)
		group := m.loadGroupCtrl(base, &groupBuf)

		for matches := matchH2(group, h2); matches != 0; matches &= matches - 1 {
			slot := base + uint64(bits.TrailingZeros16(matches))
			ok, err := m.verifyHash(m.getSlot(slot), hash)
			if err != nil {
				return false, fmt.Errorf("swiss delete: %w", err)
			}
			if ok {
				m.setCtrl(slot, ctrlDeleted)
				m.clearSlot(slot)
				m.count--
				return true, nil
			}
		}

		if matchEmpty(group) != 0 {
			return false, nil
		}
	}
	return false, nil
}

// Count returns the number of entries.
func (m *SwissPositionMap) Count() uint64 {
	return m.count
}

// ForEach iterates over all entries.
func (m *SwissPositionMap) ForEach(fn func(packed uint64)) {
	for i := range m.numSlots {
		var c byte
		if v, ok := m.ctrlOverlay[i]; ok {
			c = v
		} else {
			c = m.ctrl[i]
		}
		if c&ctrlFull != 0 {
			fn(m.getSlot(i))
		}
	}
}

// Close unmaps and closes files.
func (m *SwissPositionMap) Close() error {
	var errs []error
	if m.ctrlMmap != nil {
		if err := syscall.Munmap(m.ctrlMmap); err != nil {
			errs = append(errs, fmt.Errorf("munmap ctrl: %w", err))
		}
	}
	if m.slotsMmap != nil {
		if err := syscall.Munmap(m.slotsMmap); err != nil {
			errs = append(errs, fmt.Errorf("munmap slots: %w", err))
		}
	}
	if m.ctrlFile != nil {
		if err := m.ctrlFile.Close(); err != nil {
			errs = append(errs, fmt.Errorf("close ctrl: %w", err))
		}
	}
	if m.slotsFile != nil {
		if err := m.slotsFile.Close(); err != nil {
			errs = append(errs, fmt.Errorf("close slots: %w", err))
		}
	}
	return errors.Join(errs...)
}

// SetConsistencyHash updates the stored hash in the ctrl and slots file
// headers and flushes the mmap to disk. Call this after WAL flush succeeds
// to enable skipping rebuild on restart.
func (m *SwissPositionMap) SetConsistencyHash(hash [32]byte) error {
	// Flush mmap'd ctrl and slot data to disk before writing the consistency
	// hash. The hash acts as a "valid" marker, so all data must be durable
	// first. On Linux, fsync on the fd flushes MAP_SHARED dirty pages.
	if err := m.slotsFile.Sync(); err != nil {
		return fmt.Errorf("sync slots: %w", err)
	}
	if err := m.ctrlFile.Sync(); err != nil {
		return fmt.Errorf("sync ctrl: %w", err)
	}
	// Write through the fd (not the mmap) so that File.Sync is guaranteed
	// to flush the header data.
	if _, err := m.ctrlFile.WriteAt(hash[:], 0); err != nil {
		return fmt.Errorf("write ctrl consistency hash: %w", err)
	}
	if _, err := m.slotsFile.WriteAt(hash[:], 0); err != nil {
		return fmt.Errorf("write slots consistency hash: %w", err)
	}
	if err := m.ctrlFile.Sync(); err != nil {
		return fmt.Errorf("sync ctrl hash: %w", err)
	}
	return m.slotsFile.Sync()
}

// ----------------------------------------------------------------------------
// Internal: Hashing
// ----------------------------------------------------------------------------

// groupBase returns the byte offset of the i-th group in a linear probe
// sequence starting from the given group index. Each group has 16 slots,
// so at most 16 comparisons per group visited.
func (m *SwissPositionMap) groupBase(start, i uint64) uint64 {
	return ((start + i) % m.numGroups) * groupSize
}

// splitHash returns H1 (bucket index) and H2 (control byte).
// H1 is the first 8 bytes of the hash (used for group selection) and H2 is
// derived from byte 9 (7-bit fingerprint with high bit set). Since this map
// is only used for leaves that are already uniquely hashed, we don't need to
// worry about too many collisions happening.
func splitHash(hash [32]byte) (h1 uint64, h2 byte) {
	h1 = binary.LittleEndian.Uint64(hash[:8])
	h2 = (hash[8] & 0x7F) | ctrlFull // high bit set + 7-bit fingerprint
	return
}

// verifyHash reads the hash at the position encoded in packed and compares it
// to expected. The position (extracted via posMask) must correspond to a
// valid 32-byte hash entry in dataFile at offset position*32.
func (m *SwissPositionMap) verifyHash(packed uint64, expected [32]byte) (bool, error) {
	var buf [32]byte
	pos := packed & m.posMask
	if _, err := m.dataFile.ReadAt(buf[:], int64(pos*32)); err != nil {
		return false, fmt.Errorf("read hash at position %d: %w", pos, err)
	}
	return buf == expected, nil
}

// ----------------------------------------------------------------------------
// Internal: Overlay-aware accessors
// ----------------------------------------------------------------------------

// loadGroupCtrl returns the 16-byte ctrl group at the given base offset,
// merging any overlay entries. When no overlay entries exist for this group,
// the mmap slice is returned directly (zero-copy fast path). Otherwise the
// provided buf is filled and returned. Each caller provides its own buf so
// concurrent Get calls remain safe.
func (m *SwissPositionMap) loadGroupCtrl(base uint64, buf *[groupSize]byte) []byte {
	if len(m.dirtyGroups) == 0 {
		return m.ctrl[base : base+groupSize]
	}
	if _, dirty := m.dirtyGroups[base/groupSize]; !dirty {
		return m.ctrl[base : base+groupSize]
	}
	copy(buf[:], m.ctrl[base:base+groupSize])
	for i := range uint64(groupSize) {
		if v, ok := m.ctrlOverlay[base+i]; ok {
			buf[i] = v
		}
	}
	return buf[:]
}

// setCtrl writes a ctrl byte to the overlay (not the mmap).
func (m *SwissPositionMap) setCtrl(slot uint64, v byte) {
	m.ctrlOverlay[slot] = v
	m.dirtyGroups[slot/groupSize] = struct{}{}
}

// getSlot returns the packed value for slot i, checking the overlay first.
func (m *SwissPositionMap) getSlot(i uint64) uint64 {
	if val, ok := m.slotsOverlay[i]; ok {
		return val
	}
	return binary.LittleEndian.Uint64(m.slots[i*8:])
}

// setSlot writes a packed value to the overlay (not the mmap).
func (m *SwissPositionMap) setSlot(i uint64, val uint64) {
	m.slotsOverlay[i] = val
}

// clearSlot writes a zero packed value to the overlay (not the mmap).
func (m *SwissPositionMap) clearSlot(i uint64) {
	m.slotsOverlay[i] = 0
}

// ----------------------------------------------------------------------------
// Internal: Resize
// ----------------------------------------------------------------------------

// RebuildEntry holds precomputed hash components for sorted bulk insertion.
type RebuildEntry struct {
	group  uint32 // H1 % numGroups
	h2     byte   // H2 fingerprint (with ctrlFull bit set)
	packed uint64 // packed position + addIndex
}

// PrepareEntry computes the group and H2 from a hash for bulk rebuild.
func (m *SwissPositionMap) PrepareEntry(hash [32]byte, packed uint64) RebuildEntry {
	h1, h2 := splitHash(hash)
	return RebuildEntry{
		group:  uint32(h1 % m.numGroups),
		h2:     h2,
		packed: packed,
	}
}

// PrepareRebuild clears the table for a fresh bulk rebuild. Must be called
// before InsertBatch when the table may contain stale data or tombstones.
// Also clears the overlay since rebuild writes directly to the mmap.
func (m *SwissPositionMap) PrepareRebuild() {
	clear(m.ctrl)
	clear(m.ctrlOverlay)
	clear(m.slotsOverlay)
	clear(m.dirtyGroups)
	m.count = 0
}

// InsertBatch sorts entries by group and inserts them for sequential ctrl/slots
// access. Call PrepareRebuild once before the first InsertBatch. The entries
// slice is sorted in place.
func (m *SwissPositionMap) InsertBatch(entries []RebuildEntry) error {
	slices.SortFunc(entries, func(a, b RebuildEntry) int {
		if a.group < b.group {
			return -1
		}
		if a.group > b.group {
			return 1
		}
		return 0
	})

	for _, e := range entries {
		if err := rehashInsertPrecomputed(m.ctrl, m.slots, m.numGroups, uint64(e.group), e.h2, e.packed); err != nil {
			return err
		}
	}

	m.count += uint64(len(entries))
	return nil
}

// rehashInsertPrecomputed inserts a precomputed entry into explicit ctrl/slots
// buffers. Like rehashInsert but skips splitHash since H1 group and H2 are
// already computed.
func rehashInsertPrecomputed(ctrl []byte, slots []byte, numGroups uint64, startGroup uint64, h2 byte, packed uint64) error {
	for i := range numGroups {
		base := ((startGroup + i) % numGroups) * groupSize
		if avail := matchEmpty(ctrl[base : base+groupSize]); avail != 0 {
			slot := base + uint64(bits.TrailingZeros16(avail))
			ctrl[slot] = h2
			binary.LittleEndian.PutUint64(slots[slot*8:], packed)
			return nil
		}
	}
	return fmt.Errorf("swiss table rehash precomputed: no slot available (groups=%d)", numGroups)
}

// rehashInsert inserts a hash->packed mapping into explicit ctrl/slots buffers.
// It skips duplicate checking because it is only used during resize where the
// target table is known to be empty. This also avoids depending on m's fields,
// so the caller can defer updating m until rehash fully succeeds.
func rehashInsert(ctrl []byte, slots []byte, numGroups uint64, hash [32]byte, packed uint64) error {
	h1, h2 := splitHash(hash)
	start := h1 % numGroups

	for i := range numGroups {
		base := ((start + i) % numGroups) * groupSize
		if avail := matchEmpty(ctrl[base : base+groupSize]); avail != 0 {
			slot := base + uint64(bits.TrailingZeros16(avail))
			ctrl[slot] = h2
			binary.LittleEndian.PutUint64(slots[slot*8:], packed)
			return nil
		}
	}
	return fmt.Errorf("swiss table rehash: no slot available (groups=%d)", numGroups)
}

// resize doubles the table and rehashes all entries.
//
// This operation is not crash-safe in isolation. If the process crashes
// mid-resize, the on-disk files will contain a partial table. The consistency
// hash is invalidated before resizing so that a crash triggers a full rebuild
// from the data file on restart.
//
// Rehashing is performed into the new mmaps without updating m's fields first.
// Only after a successful rehash does the swap occur. On failure the old
// ctrl/slots are restored from saved copies so the map remains usable for the
// current session. The zeroed consistency hash ensures rebuild on restart.
//
// Overlay entries are merged into the old data before collecting entries for
// rehash, then the overlay is cleared since all entries are in the new mmap.
func (m *SwissPositionMap) resize() error {
	oldNumSlots := m.numSlots
	newNumSlots := oldNumSlots * 2
	newNumGroups := newNumSlots / groupSize

	// Copy old data before remapping. Both copies are necessary because
	// the old and new mmaps share the same underlying file (MAP_SHARED),
	// so clearing stale ctrl bytes in the new mmap would also zero the
	// overlapping region visible through the old mmap.
	//
	// We use anonymous mmap regions instead of Go heap allocations
	// (make([]byte, …)) so the memory is managed by the kernel, not Go's
	// GC. This avoids multi-GB GC pressure during repeated resizes; each
	// Munmap returns the pages to the OS immediately.
	oldCtrl, err := mmapAnon(int(oldNumSlots))
	if err != nil {
		return fmt.Errorf("resize alloc oldCtrl: %w", err)
	}
	defer munmapAnon(oldCtrl)
	copy(oldCtrl, m.ctrl)

	oldSlots, err := mmapAnon(int(oldNumSlots) * 8)
	if err != nil {
		return fmt.Errorf("resize alloc oldSlots: %w", err)
	}
	defer munmapAnon(oldSlots)
	copy(oldSlots, m.slots)

	// Merge overlay entries into old copies so they're included in rehash.
	for slot, v := range m.ctrlOverlay {
		if slot < oldNumSlots {
			oldCtrl[slot] = v
		}
	}
	for slot, v := range m.slotsOverlay {
		if slot < oldNumSlots {
			binary.LittleEndian.PutUint64(oldSlots[slot*8:], v)
		}
	}

	// Collect all occupied packed slot values and sort by data file
	// position so that hash reads are sequential rather than random.
	// Sequential access benefits from OS readahead and is orders of
	// magnitude faster than random 32-byte reads across a multi-GB file.
	entries := make([]uint64, 0, m.count)
	for i, c := range oldCtrl {
		if c&ctrlFull != 0 {
			entries = append(entries, binary.LittleEndian.Uint64(oldSlots[i*8:]))
		}
	}
	posMask := m.posMask
	slices.SortFunc(entries, func(a, b uint64) int {
		ap, bp := a&posMask, b&posMask
		if ap < bp {
			return -1
		}
		if ap > bp {
			return 1
		}
		return 0
	})

	// Invalidate consistency hash before modifying files. If the process
	// crashes during resize, the zero header ensures rebuild on restart.
	// Write through the fd (not the mmap) so that File.Sync is guaranteed
	// to flush the data per POSIX without requiring msync.
	var zeroHeader [fileHeaderSize]byte
	if _, err := m.ctrlFile.WriteAt(zeroHeader[:], 0); err != nil {
		return fmt.Errorf("resize invalidate ctrl header: %w", err)
	}
	if _, err := m.slotsFile.WriteAt(zeroHeader[:], 0); err != nil {
		return fmt.Errorf("resize invalidate slots header: %w", err)
	}
	if err := m.ctrlFile.Sync(); err != nil {
		return fmt.Errorf("resize fsync ctrl: %w", err)
	}
	if err := m.slotsFile.Sync(); err != nil {
		return fmt.Errorf("resize fsync slots: %w", err)
	}

	// Extend files (both include header)
	newCtrlFileSize := int64(fileHeaderSize + newNumSlots)
	if err := m.ctrlFile.Truncate(newCtrlFileSize); err != nil {
		return fmt.Errorf("resize ctrl: %w", err)
	}
	newSlotsFileSize := int64(fileHeaderSize + newNumSlots*8)
	if err := m.slotsFile.Truncate(newSlotsFileSize); err != nil {
		return fmt.Errorf("resize slots: %w", err)
	}

	// Remap (both mmaps include header).
	// If the second mmap fails, unmap the first to avoid a leak.
	newCtrlMmap, err := syscall.Mmap(int(m.ctrlFile.Fd()), 0, int(newCtrlFileSize),
		syscall.PROT_READ|syscall.PROT_WRITE, mmapFlags)
	if err != nil {
		return fmt.Errorf("resize ctrl mmap: %w", err)
	}
	newSlotsMmap, err := syscall.Mmap(int(m.slotsFile.Fd()), 0, int(newSlotsFileSize),
		syscall.PROT_READ|syscall.PROT_WRITE, mmapFlags)
	if err != nil {
		syscall.Munmap(newCtrlMmap)
		return fmt.Errorf("resize slots mmap: %w", err)
	}

	// Slice past headers.
	newCtrl := newCtrlMmap[fileHeaderSize:]
	newSlots := newSlotsMmap[fileHeaderSize:]

	// Clear stale ctrl bytes from the old table. Truncate only zero-fills
	// the extension; the overlapping region retains old ctrlFull/ctrlDeleted
	// bytes that would appear as ghost entries to rehashInsert and later
	// lookups.
	clear(newCtrl)

	// Rehash into the new mmaps WITHOUT updating m's fields. Entries are
	// iterated in sorted position order so hash reads are sequential. On
	// failure we restore the old ctrl/slots from saved copies so the map
	// remains usable for the current session. The zeroed consistency hash
	// ensures a full rebuild on restart.
	restoreOld := func() {
		copy(m.ctrl, oldCtrl)
		copy(m.slots, oldSlots)
		syscall.Munmap(newCtrlMmap)
		syscall.Munmap(newSlotsMmap)
	}

	for _, packed := range entries {
		var hash [32]byte
		pos := int64((packed & posMask) * 32)
		if _, err := m.dataFile.ReadAt(hash[:], pos); err != nil {
			restoreOld()
			return fmt.Errorf("resize rehash read: %w", err)
		}
		if err := rehashInsert(newCtrl, newSlots, newNumGroups, hash, packed); err != nil {
			restoreOld()
			return fmt.Errorf("resize rehash: %w", err)
		}
	}

	// Rehash succeeded — swap to new state and unmap old mmaps.
	oldCtrlMmap := m.ctrlMmap
	oldSlotsMmap := m.slotsMmap

	m.ctrlMmap = newCtrlMmap
	m.ctrl = newCtrl
	m.slotsMmap = newSlotsMmap
	m.slots = newSlots
	m.numSlots = newNumSlots
	m.numGroups = newNumGroups
	m.count = uint64(len(entries))

	syscall.Munmap(oldCtrlMmap)
	syscall.Munmap(oldSlotsMmap)

	// Clear overlay — all entries are now in the new mmap. The rehashed
	// data is written through the mmap (MAP_SHARED) and will be synced
	// during the next flush. The consistency hash was already invalidated,
	// so a crash before flush triggers rebuild.
	clear(m.ctrlOverlay)
	clear(m.slotsOverlay)
	clear(m.dirtyGroups)

	return nil
}

// ----------------------------------------------------------------------------
// WAL integration
// ----------------------------------------------------------------------------

// PendingCount returns the number of dirty overlay entries (ctrl + slots).
func (m *SwissPositionMap) PendingCount() int {
	return len(m.ctrlOverlay) + len(m.slotsOverlay)
}

// PendingCtrlOverlay returns the ctrl overlay map for size estimation.
func (m *SwissPositionMap) PendingCtrlOverlay() map[uint64]byte {
	return m.ctrlOverlay
}

// PendingSlotsOverlay returns the slots overlay map for size estimation.
func (m *SwissPositionMap) PendingSlotsOverlay() map[uint64]uint64 {
	return m.slotsOverlay
}

// ForEachPendingCtrl iterates over dirty ctrl entries. The callback receives
// the byte offset in the ctrl file and the ctrl byte value.
func (m *SwissPositionMap) ForEachPendingCtrl(fn func(fileOffset int64, value byte)) {
	for slot, v := range m.ctrlOverlay {
		fn(int64(fileHeaderSize+slot), v)
	}
}

// ForEachPendingSlot iterates over dirty slot entries. The callback receives
// the byte offset in the slots file and the packed value.
func (m *SwissPositionMap) ForEachPendingSlot(fn func(fileOffset int64, value uint64)) {
	for slot, v := range m.slotsOverlay {
		fn(int64(fileHeaderSize+slot*8), v)
	}
}

// ApplyPending writes all pending ctrl/slot overlay entries to the underlying
// files via file descriptor writes (not through the mmap). The MAP_SHARED mmap
// will reflect these changes through the shared page cache.
func (m *SwissPositionMap) ApplyPending() error {
	for slot, v := range m.ctrlOverlay {
		if _, err := m.ctrlFile.WriteAt([]byte{v}, int64(fileHeaderSize+slot)); err != nil {
			return fmt.Errorf("apply ctrl at slot %d: %w", slot, err)
		}
	}
	var buf [8]byte
	for slot, v := range m.slotsOverlay {
		binary.LittleEndian.PutUint64(buf[:], v)
		if _, err := m.slotsFile.WriteAt(buf[:], int64(fileHeaderSize+slot*8)); err != nil {
			return fmt.Errorf("apply slot at slot %d: %w", slot, err)
		}
	}
	return nil
}

// SyncFiles syncs the ctrl and slots files to disk.
func (m *SwissPositionMap) SyncFiles() error {
	if err := m.ctrlFile.Sync(); err != nil {
		return fmt.Errorf("sync ctrl: %w", err)
	}
	return m.slotsFile.Sync()
}

// ApplyConsistencyHash writes the consistency hash to both file headers
// via fd writes (not through the mmap). Unlike SetConsistencyHash, this
// does NOT sync the files — the caller is responsible for syncing.
func (m *SwissPositionMap) ApplyConsistencyHash(hash [32]byte) error {
	if _, err := m.ctrlFile.WriteAt(hash[:], 0); err != nil {
		return fmt.Errorf("write ctrl consistency hash: %w", err)
	}
	if _, err := m.slotsFile.WriteAt(hash[:], 0); err != nil {
		return fmt.Errorf("write slots consistency hash: %w", err)
	}
	return nil
}

// ClearPending drops the overlay after a successful flush. The mmap now
// reflects the flushed data via the shared page cache.
func (m *SwissPositionMap) ClearPending() {
	clear(m.ctrlOverlay)
	clear(m.slotsOverlay)
	clear(m.dirtyGroups)
	m.baseCount = m.count
}

// DiscardPending reverts the overlay and count to the pre-modification state.
// The mmap still has the original data (overlay never touched the mmap).
func (m *SwissPositionMap) DiscardPending() {
	clear(m.ctrlOverlay)
	clear(m.slotsOverlay)
	clear(m.dirtyGroups)
	m.count = m.baseCount
}
