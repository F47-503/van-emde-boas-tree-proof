import VanEmdeBoas.findNextPrev
import VanEmdeBoas.InsertProof
import VanEmdeBoas.DeleteProof

inductive vEBWrapper : Nat → Type where
| Tree {u : Nat} (tree : vEBTree u) (invariant : correctInvariants tree) : vEBWrapper u

def wrapperInsert {v : Nat} (tree : vEBWrapper v) (x : Fin (2 ^ 2 ^ v)) : vEBWrapper v :=
  match tree with
  | vEBWrapper.Tree tree invariant =>
    vEBWrapper.Tree (treeInsert tree x) (insertCorrectInvariants v tree x invariant.left invariant.right)

def wrapperDelete {v : Nat} (tree : vEBWrapper v) (x : Fin (2 ^ 2 ^ v)) : vEBWrapper v :=
  match tree with
  | vEBWrapper.Tree tree invariant =>
    vEBWrapper.Tree (treeDelete tree x) (deleteCorrectInvariants v tree x invariant.left invariant.right)

def wrapperCreate (v : Nat) : vEBWrapper v :=
  vEBWrapper.Tree (createEmpty v) (createCorrectInvariants v)

def wrapperFindNext {v : Nat} (tree : vEBWrapper v) (x : Fin (2 ^ 2 ^ v)) : Option (Fin (2 ^ 2 ^ v)) :=
  match tree with
  | vEBWrapper.Tree tree _ =>
    findNext tree x

def wrapperFindPrev {v : Nat} (tree : vEBWrapper v) (x : Fin (2 ^ 2 ^ v)) : Option (Fin (2 ^ 2 ^ v)) :=
  match tree with
  | vEBWrapper.Tree tree _ =>
    findPrev tree x

#eval wrapperFindPrev (
        wrapperInsert (
            wrapperInsert (
                wrapperCreate 6) 3) 23) 15
