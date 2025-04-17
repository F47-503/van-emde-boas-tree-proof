# van Emde Boas tree proof

## This repository contains verification of correctness for van Emde Boas Tree implemented using Lean 4

There are two branches : 
`main` - original version of the datastructure
`simplified` - simplified version, values are stored only in leaves therefore making deletion and insertion O(logM), but verification is easier