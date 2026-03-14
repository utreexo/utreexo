//go:build linux

package utreexo

import "github.com/utreexo/utreexo/internal/mmapcache"

// mmapCacheStore adapts mmapcache.Store to the unexported cacheStore
// interface used by cachedRWS.
type mmapCacheStore struct{ s *mmapcache.Store }

func newMmapCacheStore(entrySize int, maxBytes int64) *mmapCacheStore {
	return &mmapCacheStore{s: mmapcache.New(entrySize, maxBytes)}
}

func (m *mmapCacheStore) get(offset int64) ([]byte, bool) { return m.s.Get(offset) }
func (m *mmapCacheStore) put(offset int64, data []byte)   { m.s.Put(offset, data) }
func (m *mmapCacheStore) delete(offset int64)             { m.s.Delete(offset) }
func (m *mmapCacheStore) deleteAbove(size int64)          { m.s.DeleteAbove(size) }
func (m *mmapCacheStore) clear()                          { m.s.Clear() }
func (m *mmapCacheStore) forEach(fn func(int64, []byte))  { m.s.ForEach(fn) }
func (m *mmapCacheStore) overflowed() bool                { return m.s.Overflowed() }
func (m *mmapCacheStore) count() int                      { return m.s.Count() }
func (m *mmapCacheStore) entrySize() int                  { return m.s.EntrySize() }
