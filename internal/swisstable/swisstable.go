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
// Concurrent read-only access (Get) is safe.
type SwissPositionMap struct {
	// Mmap'd data
	ctrlMmap  []byte // full mmap including header
	ctrl      []byte // control bytes (1 per slot), points into ctrlMmap after header
	slotsMmap []byte // full mmap including header
	slots     []byte // packed positions (8 bytes per slot), points into slotsMmap after header

	// File handles for mmap
	ctrlFile  *os.File
	slotsFile *os.File
	ctrlPath  string
	slotsPath string

	// Table sizing
	numSlots  uint64
	numGroups uint64 // numSlots / groupSize

	// For hash verification (we don't store hashes, we verify from source)
	dataFile io.ReaderAt
	posMask  uint64 // mask to extract position from packed value

	// Entry count
	count uint64
}

// ----------------------------------------------------------------------------
// Constructor
// ----------------------------------------------------------------------------

// NewSwissPositionMap creates a new Swiss Table backed by mmap'd files.
// Returns the map and a bool indicating if rebuild is needed (consistency hash mismatch).
// Pass a zero hash to force rebuild. posMask is applied to packed values to
// extract the leaf position for hash verification against dataFile.
func NewSwissPositionMap(ctrlPath, slotsPath string, expectedEntries uint64, consistencyHash [32]byte, dataFile io.ReaderAt, posMask uint64) (*SwissPositionMap, bool, error) {
	if dataFile == nil {
		return nil, false, fmt.Errorf("dataFile must not be nil")
	}

	ctrlFile, slotsFile, ctrlMmap, slotsBytes, numSlots, needsRebuild, err := openFiles(ctrlPath, slotsPath, expectedEntries, consistencyHash)
	if err != nil {
		return nil, false, err
	}

	// ctrl and slot bytes start after header
	ctrl := ctrlMmap[fileHeaderSize:]
	slots := slotsBytes[fileHeaderSize:]

	m := &SwissPositionMap{
		ctrlMmap:  ctrlMmap,
		ctrl:      ctrl,
		slotsMmap: slotsBytes,
		slots:     slots,
		ctrlFile:  ctrlFile,
		slotsFile: slotsFile,
		ctrlPath:  ctrlPath,
		slotsPath: slotsPath,
		numSlots:  numSlots,
		numGroups: numSlots / groupSize,
		dataFile:  dataFile,
		posMask:   posMask,
	}

	// Restore count from existing data if not rebuilding
	if !needsRebuild {
		for _, c := range ctrl {
			if c&ctrlFull != 0 {
				m.count++
			}
		}
	}

	return m, needsRebuild, nil
}

// openFiles opens and mmaps the ctrl and slots files, wiping both if either
// are inconsistent. Returns the actual numSlots and needsRebuild=true if files
// were wiped (hash mismatch, size mismatch, or zero consistency hash).
// expectedEntries is only used to size new files when rebuilding; consistent
// files are reused at their on-disk size regardless of expectedEntries.
func openFiles(ctrlPath, slotsPath string, expectedEntries uint64, consistencyHash [32]byte) (
	ctrlFile, slotsFile *os.File, ctrlMmap, slotsBytes []byte, numSlots uint64, needsRebuild bool, err error) {

	// Open both files.
	ctrlFile, err = os.OpenFile(ctrlPath, os.O_RDWR|os.O_CREATE, 0644)
	if err != nil {
		return nil, nil, nil, nil, 0, false, fmt.Errorf("open ctrl: %w", err)
	}
	slotsFile, err = os.OpenFile(slotsPath, os.O_RDWR|os.O_CREATE, 0644)
	if err != nil {
		ctrlFile.Close()
		return nil, nil, nil, nil, 0, false, fmt.Errorf("open slots: %w", err)
	}

	ctrlFi, err := ctrlFile.Stat()
	if err != nil {
		ctrlFile.Close()
		slotsFile.Close()
		return nil, nil, nil, nil, 0, false, err
	}
	slotsFi, err := slotsFile.Stat()
	if err != nil {
		ctrlFile.Close()
		slotsFile.Close()
		return nil, nil, nil, nil, 0, false, err
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
				ctrlFile.Close()
				slotsFile.Close()
				return nil, nil, nil, nil, 0, false, fmt.Errorf("truncate %s: %w", wipe.name, err)
			}
			if err := wipe.f.Truncate(wipe.size); err != nil {
				ctrlFile.Close()
				slotsFile.Close()
				return nil, nil, nil, nil, 0, false, fmt.Errorf("extend %s: %w", wipe.name, err)
			}
		}
	}

	// Mmap both files.
	ctrlSize := int64(fileHeaderSize + numSlots)
	slotsSize := int64(fileHeaderSize + numSlots*8)
	ctrlMmap, err = syscall.Mmap(int(ctrlFile.Fd()), 0, int(ctrlSize),
		syscall.PROT_READ|syscall.PROT_WRITE, mmapFlags)
	if err != nil {
		ctrlFile.Close()
		slotsFile.Close()
		return nil, nil, nil, nil, 0, false, fmt.Errorf("mmap ctrl: %w", err)
	}
	slotsBytes, err = syscall.Mmap(int(slotsFile.Fd()), 0, int(slotsSize),
		syscall.PROT_READ|syscall.PROT_WRITE, mmapFlags)
	if err != nil {
		syscall.Munmap(ctrlMmap)
		ctrlFile.Close()
		slotsFile.Close()
		return nil, nil, nil, nil, 0, false, fmt.Errorf("mmap slots: %w", err)
	}

	return ctrlFile, slotsFile, ctrlMmap, slotsBytes, numSlots, needsRebuild, nil
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

	for i := range m.numGroups {
		base := m.groupBase(start, i)
		// Check slots with matching H2
		for matches := m.matchH2(base, h2); matches != 0; matches &= matches - 1 {
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
		if m.hasEmpty(base) {
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

	for i := range m.numGroups {
		base := m.groupBase(start, i)

		// Check if key exists (update in place)
		for matches := m.matchH2(base, h2); matches != 0; matches &= matches - 1 {
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
			if avail := m.matchEmptyOrDeleted(base); avail != 0 {
				firstAvail = base + uint64(bits.TrailingZeros16(avail))
				hasAvail = true
			}
		}

		// Empty slot means the key definitely doesn't exist further
		if m.hasEmpty(base) {
			break
		}
	}

	if !hasAvail {
		return fmt.Errorf("swiss table: no available slot (count=%d, slots=%d)", m.count, m.numSlots)
	}

	m.ctrl[firstAvail] = h2
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

	for i := range m.numGroups {
		base := m.groupBase(start, i)

		for matches := m.matchH2(base, h2); matches != 0; matches &= matches - 1 {
			slot := base + uint64(bits.TrailingZeros16(matches))
			ok, err := m.verifyHash(m.getSlot(slot), hash)
			if err != nil {
				return false, fmt.Errorf("swiss delete: %w", err)
			}
			if ok {
				m.ctrl[slot] = ctrlDeleted
				m.clearSlot(slot)
				m.count--
				return true, nil
			}
		}

		if m.hasEmpty(base) {
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
	for i, c := range m.ctrl {
		if c&ctrlFull != 0 {
			fn(m.getSlot(uint64(i)))
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
// Internal: Group matching (SIMD on amd64, scalar fallback in swisstable_generic.go)
// ----------------------------------------------------------------------------

func (m *SwissPositionMap) matchH2(base uint64, h2 byte) uint16 {
	return matchH2(m.ctrl[base:base+groupSize], h2)
}

func (m *SwissPositionMap) hasEmpty(base uint64) bool {
	return matchEmpty(m.ctrl[base:base+groupSize]) != 0
}

func (m *SwissPositionMap) matchEmptyOrDeleted(base uint64) uint16 {
	return matchEmptyOrDeleted(m.ctrl[base : base+groupSize])
}

// ----------------------------------------------------------------------------
// Internal: Slot access
// ----------------------------------------------------------------------------

func (m *SwissPositionMap) getSlot(i uint64) uint64 {
	return binary.LittleEndian.Uint64(m.slots[i*8:])
}

func (m *SwissPositionMap) setSlot(i uint64, val uint64) {
	binary.LittleEndian.PutUint64(m.slots[i*8:], val)
}

func (m *SwissPositionMap) clearSlot(i uint64) {
	binary.LittleEndian.PutUint64(m.slots[i*8:], 0)
}

// ----------------------------------------------------------------------------
// Internal: Resize
// ----------------------------------------------------------------------------

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

	return nil
}
