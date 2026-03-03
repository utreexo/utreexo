package utreexo

import (
	"encoding/binary"
	"fmt"
	"hash/crc32"
	"io"
	"reflect"
	"testing"

	"github.com/stretchr/testify/require"
)

// serializeEntries encodes journal entries into a byte slice (test helper).
func serializeEntries(entries []journalEntry) []byte {
	size := 0
	for _, e := range entries {
		size += entryHeaderSize + len(e.data)
	}

	buf := make([]byte, 0, size)
	for _, e := range entries {
		buf = append(buf, e.fileIdx)
		buf = binary.LittleEndian.AppendUint64(buf, uint64(e.offset))
		buf = binary.LittleEndian.AppendUint32(buf, uint32(len(e.data)))
		buf = append(buf, e.data...)
	}
	return buf
}

// crashAfterCommit simulates a crash that occurs after the journal has
// been fully written and synced, but before entries are applied to the
// underlying files. A subsequent newWAL on the same journal + files
// will replay the committed entries during recovery.
//
// The wal should not be used after calling this.
func (w *wal) crashAfterCommit() error {
	// Use a zero bestHash for testing.
	var bestHash [journalHashSize]byte

	entriesBuf := w.serializeEntries(bestHash)
	if len(entriesBuf) == 0 {
		return fmt.Errorf("wal crash: nothing to commit")
	}
	totalLen := uint64(len(entriesBuf))

	var header [journalHeaderSize]byte
	binary.LittleEndian.PutUint64(header[:], totalLen)

	// CRC over header + bestHash + entries.
	crc := crc32.NewIEEE()
	crc.Write(header[:])
	crc.Write(bestHash[:])
	crc.Write(entriesBuf)
	var checksumBuf [journalChecksumSize]byte
	binary.LittleEndian.PutUint32(checksumBuf[:], crc.Sum32())

	if _, err := w.journal.Seek(0, io.SeekStart); err != nil {
		return err
	}
	if _, err := w.journal.Write(header[:]); err != nil {
		return err
	}
	if _, err := w.journal.Write(bestHash[:]); err != nil {
		return err
	}
	if _, err := w.journal.Write(entriesBuf); err != nil {
		return err
	}
	if _, err := w.journal.Write(checksumBuf[:]); err != nil {
		return err
	}

	// Journal is committed but entries are NOT applied. Power off.
	return nil
}

// crashBeforeCommit simulates a crash that occurs while the journal is
// being written, before the checksum is flushed. The journal will be
// incomplete, so a subsequent newWAL will discard it and the underlying
// files will remain at their previous consistent state.
//
// The wal should not be used after calling this.
func (w *wal) crashBeforeCommit() error {
	// Use a zero bestHash for testing.
	var bestHash [journalHashSize]byte

	entriesBuf := w.serializeEntries(bestHash)
	if len(entriesBuf) == 0 {
		return fmt.Errorf("wal crash: nothing to commit")
	}
	totalLen := uint64(len(entriesBuf))

	var header [journalHeaderSize]byte
	binary.LittleEndian.PutUint64(header[:], totalLen)

	if _, err := w.journal.Seek(0, io.SeekStart); err != nil {
		return err
	}
	if _, err := w.journal.Write(header[:]); err != nil {
		return err
	}
	if _, err := w.journal.Write(bestHash[:]); err != nil {
		return err
	}
	if _, err := w.journal.Write(entriesBuf); err != nil {
		return err
	}

	// Checksum NOT written. Power off.
	return nil
}

// TestWALBasicFlush verifies that data only reaches underlying files after Flush.
func TestWALBasicFlush(t *testing.T) {
	journal := newMemFile()
	files := [4]*memFile{newMemFile(), newMemFile(), newMemFile(), newMemFile()}

	w, err := newWAL(journal, files[0],
		walFile{File: files[1], EntrySize: 32},
		walFile{File: files[2], EntrySize: 4},
		walFile{File: files[3], EntrySize: 32}, // metaFile
	)
	require.NoError(t, err)

	// Write a hash to file 0.
	h := testHashFromInt(1)
	_, err = w.Cached(0).Seek(0, io.SeekStart)
	require.NoError(t, err)
	_, err = w.Cached(0).Write(h[:])
	require.NoError(t, err)

	// Mark a position as deleted in the bitmap (backed by files[0]).
	w.Bitmap().set(42)

	// Write 4 bytes to addIndex (Cached(1)).
	_, err = w.Cached(1).Seek(0, io.SeekStart)
	require.NoError(t, err)
	err = binary.Write(w.Cached(1), binary.LittleEndian, int32(7))
	require.NoError(t, err)

	// Underlying files should still be empty.
	require.Equal(t, 0, len(files[0].data), "file 0 should be empty before Flush")
	require.Equal(t, 0, len(files[1].data), "file 1 should be empty before Flush")
	require.Equal(t, 0, len(files[2].data), "file 2 should be empty before Flush")
	require.Equal(t, 0, len(files[3].data), "file 3 should be empty before Flush")

	// Flush.
	require.NoError(t, w.Flush([32]byte{}))

	// Now underlying files should have data.
	// files[0] = bitmap, files[1] = main, files[2] = addIndex, files[3] = meta
	require.Equal(t, 8, len(files[0].data), "bitmap should have 8 bytes after Flush (one word)")
	require.Equal(t, 32, len(files[1].data), "main should have 32 bytes after Flush")
	require.Equal(t, 4, len(files[2].data), "addIndex should have 4 bytes after Flush")
	require.Equal(t, 64, len(files[3].data), "meta should have 64 bytes after Flush (consistency hash at offset 32)")

	// Verify the data is correct.
	var gotHash Hash
	copy(gotHash[:], files[1].data)
	require.Equal(t, h, gotHash)

	// Bitmap word 0 should have bit 42 set.
	gotWord := binary.LittleEndian.Uint64(files[0].data)
	require.NotZero(t, gotWord&(1<<42), "bit 42 should be set in bitmap word")

	gotIdx := int32(binary.LittleEndian.Uint32(files[2].data))
	require.Equal(t, int32(7), gotIdx)

	// Caches should be empty after flush.
	require.Equal(t, 0, w.Cached(0).cache.count())
	require.Equal(t, 0, len(w.Bitmap().dirtyWords), "bitmap dirty tracking should be cleared")
	require.Equal(t, 0, w.Cached(1).cache.count())
	require.Equal(t, 0, w.Cached(2).cache.count())

	// Journal should be cleared (totalLen = 0).
	_, err = journal.Seek(0, io.SeekStart)
	require.NoError(t, err)
	var totalLen uint64
	err = binary.Read(journal, binary.LittleEndian, &totalLen)
	require.NoError(t, err)
	require.Equal(t, uint64(0), totalLen)
}

// TestWALRecovery simulates a crash after the journal is committed but
// before entries are applied to the underlying files. Recovery should
// replay the journal.
func TestWALRecovery(t *testing.T) {
	journal := newMemFile()
	files := [4]*memFile{newMemFile(), newMemFile(), newMemFile(), newMemFile()}

	// Build a valid journal manually (simulating a committed Flush
	// that crashed before applying to underlying files).
	h := testHashFromInt(99)
	entries := []journalEntry{
		{fileIdx: 0, offset: 0, data: h[:]},
		{fileIdx: 1, offset: 0, data: []byte{5, 0, 0, 0}},             // addIndex=5
		{fileIdx: 2, offset: 32, data: make([]byte, 32)},              // consistency hash
		{fileIdx: 3, offset: 0, data: []byte{1, 0, 0, 0, 0, 0, 0, 0}}, // deleted bitmap word
	}
	entriesBuf := serializeEntries(entries)
	totalLen := uint64(len(entriesBuf))

	// Write valid journal with new format: header + bestHash + entries + checksum.
	var header [journalHeaderSize]byte
	binary.LittleEndian.PutUint64(header[:], totalLen)

	var bestHash [journalHashSize]byte // zero hash for testing

	crc := crc32.NewIEEE()
	crc.Write(header[:])
	crc.Write(bestHash[:])
	crc.Write(entriesBuf)
	var checksumBuf [journalChecksumSize]byte
	binary.LittleEndian.PutUint32(checksumBuf[:], crc.Sum32())

	_, err := journal.Write(header[:])
	require.NoError(t, err)
	_, err = journal.Write(bestHash[:])
	require.NoError(t, err)
	_, err = journal.Write(entriesBuf)
	require.NoError(t, err)
	_, err = journal.Write(checksumBuf[:])
	require.NoError(t, err)

	// Underlying files are empty (simulating crash before apply).
	require.Equal(t, 0, len(files[0].data))
	require.Equal(t, 0, len(files[1].data))
	require.Equal(t, 0, len(files[2].data))
	require.Equal(t, 0, len(files[3].data))

	// Create WAL — recovery should replay the journal.
	w, err := newWAL(journal, files[0],
		walFile{File: files[1], EntrySize: 32},
		walFile{File: files[2], EntrySize: 4},
		walFile{File: files[3], EntrySize: 32}, // metaFile
	)
	require.NoError(t, err)

	// Underlying files should now have the recovered data.
	// files[0] = bitmap, files[1] = main, files[2] = addIndex, files[3] = meta
	require.Equal(t, 8, len(files[0].data), "bitmap should be recovered")
	require.Equal(t, 32, len(files[1].data), "main should be recovered")
	require.Equal(t, 4, len(files[2].data), "addIndex should be recovered")
	require.Equal(t, 64, len(files[3].data), "meta should be recovered")

	var gotHash Hash
	copy(gotHash[:], files[1].data)
	require.Equal(t, h, gotHash)

	// Journal should be cleared after recovery.
	_, err = journal.Seek(0, io.SeekStart)
	require.NoError(t, err)
	var recoveredLen uint64
	err = binary.Read(journal, binary.LittleEndian, &recoveredLen)
	require.NoError(t, err)
	require.Equal(t, uint64(0), recoveredLen)

	// cachedRWS should reflect the recovered underlying state.
	require.Equal(t, int64(32), w.Cached(0).baseSize)
	// files[0] (bitmap) is loaded into w.Bitmap(), not cachedRWS.
	require.Equal(t, 8, len(files[0].data), "bitmap file should have 8 bytes after recovery")
	require.True(t, w.Bitmap().isSet(0), "bit 0 should be set in recovered bitmap")
	require.Equal(t, 1, w.Bitmap().count(), "recovered bitmap should have exactly 1 bit set")
	require.Equal(t, int64(4), w.Cached(1).baseSize)
	require.Equal(t, int64(64), w.Cached(2).baseSize)
}

// TestWALIncompleteJournal simulates a crash during journal write (before
// the checksum is fully written). Recovery should discard the incomplete
// journal and leave underlying files unchanged.
func TestWALIncompleteJournal(t *testing.T) {
	journal := newMemFile()
	files := [4]*memFile{newMemFile(), newMemFile(), newMemFile(), newMemFile()}

	// Pre-populate main file (files[1]) with known data.
	origHash := testHashFromInt(1)
	_, err := files[1].Write(origHash[:])
	require.NoError(t, err)

	// Write a journal with valid header + bestHash + entries but NO checksum
	// (simulating crash mid-write).
	badHash := testHashFromInt(999)
	entries := []journalEntry{
		{fileIdx: 0, offset: 0, data: badHash[:]},
	}
	entriesBuf := serializeEntries(entries)
	totalLen := uint64(len(entriesBuf))

	var header [journalHeaderSize]byte
	binary.LittleEndian.PutUint64(header[:], totalLen)

	var bestHash [journalHashSize]byte

	_, err = journal.Write(header[:])
	require.NoError(t, err)
	_, err = journal.Write(bestHash[:])
	require.NoError(t, err)
	_, err = journal.Write(entriesBuf)
	require.NoError(t, err)
	// Intentionally omit checksum.

	// Create WAL — should discard incomplete journal.
	_, err = newWAL(journal, files[0],
		walFile{File: files[1], EntrySize: 32},
		walFile{File: files[2], EntrySize: 4},
		walFile{File: files[3], EntrySize: 32}, // metaFile
	)
	require.NoError(t, err)

	// Main file should still have the original data.
	var gotHash Hash
	copy(gotHash[:], files[1].data[:32])
	require.Equal(t, origHash, gotHash)
}

// TestWALCorruptChecksum verifies that a journal with a bad checksum
// is discarded during recovery.
func TestWALCorruptChecksum(t *testing.T) {
	journal := newMemFile()
	files := [4]*memFile{newMemFile(), newMemFile(), newMemFile(), newMemFile()}

	origHash := testHashFromInt(1)
	_, err := files[1].Write(origHash[:])
	require.NoError(t, err)

	// Write complete journal with WRONG checksum.
	badHash := testHashFromInt(999)
	entries := []journalEntry{
		{fileIdx: 0, offset: 0, data: badHash[:]},
	}
	entriesBuf := serializeEntries(entries)
	totalLen := uint64(len(entriesBuf))

	var header [journalHeaderSize]byte
	binary.LittleEndian.PutUint64(header[:], totalLen)

	var bestHash [journalHashSize]byte

	_, err = journal.Write(header[:])
	require.NoError(t, err)
	_, err = journal.Write(bestHash[:])
	require.NoError(t, err)
	_, err = journal.Write(entriesBuf)
	require.NoError(t, err)

	// Write a bad checksum.
	var badChecksum [journalChecksumSize]byte
	binary.LittleEndian.PutUint32(badChecksum[:], 0xDEADBEEF)
	_, err = journal.Write(badChecksum[:])
	require.NoError(t, err)

	// Create WAL — should discard corrupt journal.
	_, err = newWAL(journal, files[0],
		walFile{File: files[1], EntrySize: 32},
		walFile{File: files[2], EntrySize: 4},
		walFile{File: files[3], EntrySize: 32}, // metaFile
	)
	require.NoError(t, err)

	// Main file should still have the original data.
	var gotHash Hash
	copy(gotHash[:], files[1].data[:32])
	require.Equal(t, origHash, gotHash)
}

// TestWALRequiresThreeFiles ensures newWAL only accepts exactly 3 files.
func TestWALRequiresThreeFiles(t *testing.T) {
	tests := []struct {
		name       string
		fileCount  int
		expectFail bool
	}{
		{name: "zero", fileCount: 0, expectFail: true},
		{name: "one", fileCount: 1, expectFail: true},
		{name: "two", fileCount: 2, expectFail: true},
		{name: "three", fileCount: 3, expectFail: false},
		{name: "four", fileCount: 4, expectFail: true},
		{name: "five", fileCount: 5, expectFail: true},
	}

	entrySizes := []int{32, 4, 32, 32, 32}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			journal := newMemFile()
			bitmapFile := newMemFile()
			files := make([]walFile, tc.fileCount)
			for i := 0; i < tc.fileCount; i++ {
				files[i] = walFile{File: newMemFile(), EntrySize: entrySizes[i%len(entrySizes)]}
			}

			_, err := newWAL(journal, bitmapFile, files...)
			if tc.expectFail {
				require.Error(t, err)
				require.Contains(t, err.Error(), "exactly 3 files")
			} else {
				require.NoError(t, err)
			}
		})
	}
}

// TestWALOversizeTotalLen ensures recovery clears journals with oversized totalLen values.
func TestWALOversizeTotalLen(t *testing.T) {
	tests := []struct {
		name     string
		totalLen uint64
	}{
		{name: "exceeds-file-size", totalLen: 1000},
		{name: "max-int64-plus-one", totalLen: ^uint64(0)>>1 + 1},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			journal := newMemFile()
			files := [4]*memFile{newMemFile(), newMemFile(), newMemFile(), newMemFile()}

			// Pre-populate files to detect unintended recovery writes.
			origHash := testHashFromInt(7)
			_, err := files[0].Write([]byte{1, 2, 3, 4, 5, 6, 7, 8})
			require.NoError(t, err)
			_, err = files[1].Write(origHash[:])
			require.NoError(t, err)
			_, err = files[2].Write([]byte{9, 10, 11, 12})
			require.NoError(t, err)
			_, err = files[3].Write(make([]byte, 64))
			require.NoError(t, err)

			// Write a header with a totalLen that exceeds the file size bounds.
			var header [journalHeaderSize]byte
			binary.LittleEndian.PutUint64(header[:], tc.totalLen)
			_, err = journal.Write(header[:])
			require.NoError(t, err)

			// Pad to journalMinSize so recovery attempts to read the header.
			_, err = journal.Write(make([]byte, journalMinSize-journalHeaderSize))
			require.NoError(t, err)

			_, err = newWAL(journal, files[0],
				walFile{File: files[1], EntrySize: 32},
				walFile{File: files[2], EntrySize: 4},
				walFile{File: files[3], EntrySize: 32}, // metaFile
			)
			require.NoError(t, err)

			// Journal should be cleared.
			_, err = journal.Seek(0, io.SeekStart)
			require.NoError(t, err)
			var totalLen uint64
			err = binary.Read(journal, binary.LittleEndian, &totalLen)
			require.NoError(t, err)
			require.Equal(t, uint64(0), totalLen)

			// Underlying files should remain unchanged.
			require.Equal(t, []byte{1, 2, 3, 4, 5, 6, 7, 8}, files[0].data)
			var gotHash Hash
			copy(gotHash[:], files[1].data[:32])
			require.Equal(t, origHash, gotHash)
			require.Equal(t, []byte{9, 10, 11, 12}, files[2].data)
			require.Equal(t, 64, len(files[3].data))
		})
	}
}

// TestWALDiscard verifies that Discard drops pending writes and reverts bitmap.
func TestWALDiscard(t *testing.T) {
	journal := newMemFile()
	files := [4]*memFile{newMemFile(), newMemFile(), newMemFile(), newMemFile()}

	w, err := newWAL(journal, files[0],
		walFile{File: files[1], EntrySize: 32},
		walFile{File: files[2], EntrySize: 4},
		walFile{File: files[3], EntrySize: 32}, // metaFile
	)
	require.NoError(t, err)

	// Write data to cache.
	h := testHashFromInt(1)
	_, err = w.Cached(0).Seek(0, io.SeekStart)
	require.NoError(t, err)
	_, err = w.Cached(0).Write(h[:])
	require.NoError(t, err)

	// Mutate bitmap.
	w.Bitmap().set(42)
	require.True(t, w.Bitmap().isSet(42), "bit 42 should be set before discard")

	// Discard.
	require.NoError(t, w.Discard())

	// Underlying should be empty.
	require.Equal(t, 0, len(files[1].data))

	// Caches should be empty.
	require.Equal(t, 0, w.Cached(0).cache.count())

	// Bitmap should be reverted (bit 42 was never flushed).
	require.False(t, w.Bitmap().isSet(42), "bit 42 should be reverted after discard")

	// Flush after discard still writes consistency hash to metaFile.
	require.NoError(t, w.Flush([32]byte{}))
	require.Equal(t, 0, len(files[1].data))
	require.Equal(t, 0, len(files[0].data), "bitmap file should be empty (no dirty words)")
	require.Equal(t, 64, len(files[3].data), "metaFile should have consistency hash")
}

// TestWALMultipleFlushes verifies two successive flushes accumulate data.
func TestWALMultipleFlushes(t *testing.T) {
	journal := newMemFile()
	files := [4]*memFile{newMemFile(), newMemFile(), newMemFile(), newMemFile()}

	w, err := newWAL(journal, files[0],
		walFile{File: files[1], EntrySize: 32},
		walFile{File: files[2], EntrySize: 4},
		walFile{File: files[3], EntrySize: 32}, // metaFile
	)
	require.NoError(t, err)

	// First flush: write hash at offset 0.
	h1 := testHashFromInt(1)
	_, err = w.Cached(0).Seek(0, io.SeekStart)
	require.NoError(t, err)
	_, err = w.Cached(0).Write(h1[:])
	require.NoError(t, err)
	require.NoError(t, w.Flush([32]byte{}))

	require.Equal(t, 32, len(files[1].data))

	// Second flush: write hash at offset 32.
	h2 := testHashFromInt(2)
	_, err = w.Cached(0).Seek(32, io.SeekStart)
	require.NoError(t, err)
	_, err = w.Cached(0).Write(h2[:])
	require.NoError(t, err)
	require.NoError(t, w.Flush([32]byte{}))

	require.Equal(t, 64, len(files[1].data))

	// Verify both hashes.
	var got Hash
	copy(got[:], files[1].data[0:32])
	require.Equal(t, h1, got)
	copy(got[:], files[1].data[32:64])
	require.Equal(t, h2, got)

	// baseSize should reflect the accumulated writes.
	require.Equal(t, int64(64), w.Cached(0).baseSize)
}

// TestWALEmptyFlush verifies that Flush with no pending cache writes
// still writes the consistency hash to metaFile.
func TestWALEmptyFlush(t *testing.T) {
	journal := newMemFile()
	files := [4]*memFile{newMemFile(), newMemFile(), newMemFile(), newMemFile()}

	w, err := newWAL(journal, files[0],
		walFile{File: files[1], EntrySize: 32},
		walFile{File: files[2], EntrySize: 4},
		walFile{File: files[3], EntrySize: 32}, // metaFile
	)
	require.NoError(t, err)

	require.NoError(t, w.Flush([32]byte{}))
	require.Equal(t, 0, len(files[1].data))
	require.Equal(t, 64, len(files[3].data), "metaFile should have consistency hash")
}

// TestWALForestIntegration tests Forest backed by WAL over multiple blocks,
// comparing roots with a reference Pollard.
func TestWALForestIntegration(t *testing.T) {
	journal := newMemFile()
	mainFile := newMemFile()
	delFile := newMemFile()
	addIdxFile := newMemFile()
	metaFile := newMemFile()

	w, err := newWAL(journal, delFile,
		walFile{File: mainFile, EntrySize: 32},
		walFile{File: addIdxFile, EntrySize: 4},
		walFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	tmpDir := t.TempDir()
	forest, err := newForest(w.Cached(0), w.Cached(1), w.Cached(2), w.Bitmap(), tmpDir+"/ctrl", tmpDir+"/slots", 10)
	require.NoError(t, err)

	pollard := NewAccumulator()

	// Run 20 blocks through simChain.
	sc := newSimChainWithSeed(0x07, 0x07)

	for b := 0; b <= 20; b++ {
		adds, _, delHashes := sc.NextBlock(3)

		proof, err := pollard.Prove(delHashes)
		require.NoError(t, err)

		forestProof, err := forest.Prove(delHashes)
		require.NoError(t, err)

		err = forest.Modify(adds, delHashes, forestProof)
		require.NoError(t, err)

		err = pollard.Modify(adds, delHashes, proof)
		require.NoError(t, err)

		forestRoots := forest.GetRoots()
		pollardRoots := pollard.GetRoots()
		require.True(t, reflect.DeepEqual(forestRoots, pollardRoots),
			"block %d: roots differ", b)
	}

	// Flush through WAL.
	require.NoError(t, w.Flush([32]byte{}))

	// Restart forest from flushed underlying files and verify roots match.
	tmpDir2 := t.TempDir()
	bitmap2, err := loadDeletedBitmap(delFile)
	require.NoError(t, err)
	forest2, err := newForest(mainFile, addIdxFile, metaFile, bitmap2, tmpDir2+"/ctrl", tmpDir2+"/slots", 10)
	require.NoError(t, err)
	require.Equal(t, forest.GetRoots(), forest2.GetRoots(),
		"roots should match after restart from WAL-flushed data")
}

// TestWALForestRecovery simulates a crash after WAL journal commit but
// before applying to underlying files. On recovery, the forest should
// be in the correct state.
func TestWALForestRecovery(t *testing.T) {
	journal := newMemFile()
	mainFile := newMemFile()
	delFile := newMemFile()
	addIdxFile := newMemFile()
	metaFile := newMemFile()

	w, err := newWAL(journal, delFile,
		walFile{File: mainFile, EntrySize: 32},
		walFile{File: addIdxFile, EntrySize: 4},
		walFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	tmpDir := t.TempDir()
	forest, err := newForest(w.Cached(0), w.Cached(1), w.Cached(2), w.Bitmap(), tmpDir+"/ctrl", tmpDir+"/slots", 10)
	require.NoError(t, err)

	pollard := NewAccumulator()

	// Add 8 leaves.
	leaves := make([]Leaf, 8)
	for i := range leaves {
		leaves[i] = Leaf{Hash: testHashFromInt(i + 1)}
	}
	err = forest.Modify(leaves, nil, Proof{})
	require.NoError(t, err)
	err = pollard.Modify(leaves, nil, Proof{})
	require.NoError(t, err)

	// Flush block 1 — this completes normally.
	require.NoError(t, w.Flush([32]byte{}))

	// Now delete 2 leaves (block 2).
	delHashes := []Hash{leaves[0].Hash, leaves[3].Hash}
	forestProof, err := forest.Prove(delHashes)
	require.NoError(t, err)
	err = forest.Modify(nil, delHashes, forestProof)
	require.NoError(t, err)

	pollardProof, err := pollard.Prove(delHashes)
	require.NoError(t, err)
	err = pollard.Modify(nil, delHashes, pollardProof)
	require.NoError(t, err)

	// Save the expected roots and bitmap state for block 2.
	expectedRoots := forest.GetRoots()
	expectedDeletedCount := w.Bitmap().count()
	require.Greater(t, expectedDeletedCount, 0, "deletions should have marked positions in bitmap")

	// Simulate crash: journal committed but not applied.
	require.NoError(t, w.crashAfterCommit())

	// Underlying files still only have block 1 data (crash before apply).
	// Now "restart": create a new WAL which should recover from journal.
	w2, err := newWAL(journal, delFile,
		walFile{File: mainFile, EntrySize: 32},
		walFile{File: addIdxFile, EntrySize: 4},
		walFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	// Build forest from recovered underlying files.
	tmpDir2 := t.TempDir()
	forest2, err := newForest(
		w2.Cached(0), w2.Cached(1), w2.Cached(2), w2.Bitmap(), tmpDir2+"/ctrl", tmpDir2+"/slots", 10,
	)
	require.NoError(t, err)

	// Roots should match the expected post-block-2 state.
	require.Equal(t, expectedRoots, forest2.GetRoots(),
		"roots should match after WAL recovery")

	// Bitmap should reflect the deleted positions from block 2.
	require.Equal(t, expectedDeletedCount, w2.Bitmap().count(),
		"recovered bitmap should have same number of deleted positions")
}

// TestWALCrashBeforeCommit simulates a crash during journal write (before
// the checksum is flushed). The underlying files should remain at the
// pre-crash state after recovery.
func TestWALCrashBeforeCommit(t *testing.T) {
	journal := newMemFile()
	mainFile := newMemFile()
	delFile := newMemFile()
	addIdxFile := newMemFile()
	metaFile := newMemFile()

	w, err := newWAL(journal, delFile,
		walFile{File: mainFile, EntrySize: 32},
		walFile{File: addIdxFile, EntrySize: 4},
		walFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	tmpDir := t.TempDir()
	forest, err := newForest(w.Cached(0), w.Cached(1), w.Cached(2), w.Bitmap(), tmpDir+"/ctrl", tmpDir+"/slots", 10)
	require.NoError(t, err)

	pollard := NewAccumulator()

	// Add 8 leaves (block 1).
	leaves := make([]Leaf, 8)
	for i := range leaves {
		leaves[i] = Leaf{Hash: testHashFromInt(i + 1)}
	}
	err = forest.Modify(leaves, nil, Proof{})
	require.NoError(t, err)
	err = pollard.Modify(leaves, nil, Proof{})
	require.NoError(t, err)

	// Flush block 1 — this completes normally.
	require.NoError(t, w.Flush([32]byte{}))

	// Save the expected roots from block 1.
	block1Roots := forest.GetRoots()

	// Now delete 2 leaves (block 2).
	delHashes := []Hash{leaves[0].Hash, leaves[3].Hash}
	forestProof, err := forest.Prove(delHashes)
	require.NoError(t, err)
	err = forest.Modify(nil, delHashes, forestProof)
	require.NoError(t, err)

	// Simulate crash: journal written but checksum NOT flushed.
	require.NoError(t, w.crashBeforeCommit())

	// "Restart": create a new WAL which should discard incomplete journal.
	w2, err := newWAL(journal, delFile,
		walFile{File: mainFile, EntrySize: 32},
		walFile{File: addIdxFile, EntrySize: 4},
		walFile{File: metaFile, EntrySize: 32},
	)
	require.NoError(t, err)

	// Build forest from underlying files — should be at block 1 state.
	tmpDir2 := t.TempDir()
	forest2, err := newForest(
		w2.Cached(0), w2.Cached(1), w2.Cached(2), w2.Bitmap(), tmpDir2+"/ctrl", tmpDir2+"/slots", 10,
	)
	require.NoError(t, err)

	require.Equal(t, block1Roots, forest2.GetRoots(),
		"roots should match block 1 state after discarding incomplete journal")
}

// TestWALFlushNeeded verifies that FlushNeeded returns true when a cache
// exceeds its memory threshold.
func TestWALFlushNeeded(t *testing.T) {
	journal := newMemFile()
	files := [4]*memFile{newMemFile(), newMemFile(), newMemFile(), newMemFile()}

	// Use a tiny MaxCacheBytes for file 0 so it overflows quickly.
	w, err := newWAL(journal, files[0],
		walFile{File: files[1], EntrySize: 32, MaxCacheBytes: 100},
		walFile{File: files[2], EntrySize: 4},
		walFile{File: files[3], EntrySize: 32},
	)
	require.NoError(t, err)

	// Initially, no flush needed.
	require.False(t, w.FlushNeeded(), "should not need flush initially")

	// Write enough entries to overflow the tiny cache.
	for i := range 100 {
		h := testHashFromInt(i)
		_, err = w.Cached(0).Seek(int64(i)*32, io.SeekStart)
		require.NoError(t, err)
		_, err = w.Cached(0).Write(h[:])
		require.NoError(t, err)
	}

	require.True(t, w.FlushNeeded(), "should need flush after overflowing cache")

	// After flush, FlushNeeded should be false again.
	require.NoError(t, w.Flush([32]byte{}))
	require.False(t, w.FlushNeeded(), "should not need flush after Flush")
}
