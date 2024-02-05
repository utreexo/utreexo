Utreexo
--------

A hash based dynamic accumulator based on a merkle forest

Installation
-----------

	go get github.com/utreexo/utreexo

Requirements
-----------

* Need at least `go1.18` or newer.

Usage
-----------

Utreexo is a data structure made of a collection of merkle trees.
It allows for a compact representation of a set of elements and supports the following
4 operations:

- Add Elements
- Remove Elements
- Prove Elements
- Verify Merkle Proofs

Detailed writeup with playground links on the 4 operations are available at this [Github Gist](https://gist.github.com/kcalvinalvin/a790d524832e1b7f96a70c642315fffc).

A prover keeps the entire merkle forest and is able to support all 4 operations.

A verifier only keeps the roots of the merkle forest and is not able to support
proving elements. However, a verifier may choose to cache proof for some elements
and be able to prove those specific elements.

```go
// Prover supports all 4 operations.
prover := utreexo.NewAccumulator(true)

// Verifer does not support proving elements.
verifier := utreexo.Stump{}

// A verifier may keep the below to cache the leaves and the merkle branches
// for some of the elements.
cachedHashes := []utreexo.Hash{}
cachedProof := utreexo.Proof{}
```

Add :
```go
data := []string{"utxo1", "utxo2", "utxo3", "utxo4"} 

// Hash the data as the accumulator expects []utreexo.Hash (utreexo.Hash is just [32]byte).
// These hashes are commitments to the elements we're adding.
hashes := make([]utreexo.Hash, len(data))
leaves := make([]utreexo.Leaf, len(data))
for i, d := range data {
  hash := sha256.Sum256([]byte(d))
  hashes[i] = hash
  leaves[i] = utreexo.Leaf{Hash: hash}
}

// Add the elements to the prover and the verifier.
prover.Modify(leaves, nil, nil)

updateData, _ := verifier.Update(nil, hashes, Proof{})

// If we want to cache the proof for "utxo4", we give the index of the element to cache.
rememberIndexes := []uint32{3}
cachedHashes, _ = cachedProof.Update(cachedHashes, hashes, nil, rememberIndexes, updateData)
```

Delete :
```go
// Now let's delete the element "utxo1" from the accumulator.
//
// For deletion, we first need to first prove the hashes of the elements being deleted.
proof, _ := prover.Prove(hashes[:1])

// Delete "utxo1" from the accumulator.
prover.Modify(nil, hashes[:1], proof.Targets)

// For the verifier, we need to first verify the proof before updating the state as
// the prover may give out false proofs.
_, err := utreexo.Verify(verifier, hashes[:1], proof)
if err != nil {
  fmt.Printf("Verify fail for proof %s. Error: %v\n", proof.String(), err)
  os.Exit(1)
}

// If the proof is correct, we can now modify the state of the verifier and delete "utxo1".
updateData, _ = verifier.Update(hashes[:1], nil, proof)

// Update the proof cache.
cachedHashes, _ = cachedProof.Update(cachedHashes, hashes[:1], proof.Targets, nil, updateData)
```
