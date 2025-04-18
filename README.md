# van Emde Boas tree proof

## Data structure
van Emde Boas Tree is an associative array which operates on a universe of keys of size M and supports operations in O(loglogM):

`treeInsert x` - insert `x` to the tree

`treeDelete x` - delete `x` from the tree

`findNext x` - find first element in the tree which is greater than `x` 

`findPrev x` - find last element in the tree which is less than `x`

## Versions

There are two branches : 

`main` - original version of the datastructure

`simplified` - simplified version, values are stored only in leaves therefore making deletion and insertion O(logM), but verification is easier

## Structure
`Defs` - definitions for the data structure and pair for sqrt decomposition

`UtilLemmas` - different technical lemmas (mostly about number theory involved)

`Operations` - definitions of operations like `treeDelete`, `treeInsert`

`Invariants` - definitions of invariants - correct minimum in tree, correct findPrev and others

`DeleteProof` - proofs that `treeDelete` preserves invariants together with technical lemmas

`InsertProof` - proofs that `treeInsert` preserves invariants together with technical lemmas

`findNextPrev` - proofs that under invariants `findNext` and `findPrev` are correct

`Main` - simple example with wrapper