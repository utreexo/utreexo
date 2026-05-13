package utreexo

func (f *Forest) readHashForProof(position uint64, snap *ForestView) (Hash, error) {
	if DetectRow(position, f.forestRows) == 0 && snap.bitmap.isSet(position) {
		return empty, nil
	}
	return f.readHashAt(position)
}
