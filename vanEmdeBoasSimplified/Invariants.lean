import vanEmdeBoasSimplified.Operations

--tree does not contain elements
def containsNothing {v : Nat} (tree : vEBTree v) : Prop :=
  ∀ i, ¬contains tree i

--correct minimum/maximum field
def correctSummary {v : Nat} (tree : vEBTree v) : Prop :=
  match v with
  | 0 =>
    match tree with
    | vEBTree.Leaf _ => True
  | _ + 1 =>
    match tree with
    | vEBTree.Node _ summary aux clusters =>
      (correctSummary aux ∧
      ∀ i, correctSummary (clusters i)) ∧
      match summary with
      | some (mi, ma) =>
        (contains tree mi ∧
        ∀ i, contains tree i → mi ≤ i) ∧
        (contains tree ma ∧
        ∀ i, contains tree i → i ≤ ma)
      | none =>
        --if field is empty, we should have empty auxiliary tree as well
        containsNothing tree ∧ isEmpty aux

--correct minimum/maximum field but only recursive parts
def recursiveCorrectSummary {v : Nat} (tree : vEBTree v) : Prop :=
  match v with
  | 0 =>
    match tree with
    | vEBTree.Leaf _ => True
  | _ + 1 =>
    match tree with
    | vEBTree.Node _ _ aux clusters =>
      (correctSummary aux ∧
      ∀ i, correctSummary (clusters i))

--correct interpretation of auxiliary tree
def correctAux {v : Nat} (tree : vEBTree v) : Prop :=
  match v with
  | 0 => True
  | u + 1 =>
    match tree with
    | vEBTree.Node _ _ aux clusters =>
      (correctAux aux) ∧
      (∀ i : Fin (2 ^ 2 ^ u), correctAux (clusters i)) ∧
      (∀ i : Fin (2 ^ 2 ^ u), isEmpty (clusters i) ↔ ¬contains aux i)

--if result is none, x is at least maximum,
--otherwise each element is either less-equal of x or result is less equal than element
def correctFindNext {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) : Prop :=
  (∃ res, some res = findNext tree x ∧ x < res ∧ contains tree res ∧ (∀ i, contains tree i → i ≤ x ∨ res ≤ i))
  ∨ findNext tree x = none ∧ (∀ i, contains tree i → i ≤ x)

--if result is none, x is at most minimum,
--otherwise each element is either less-equal of result or x is less equal than element
def correctFindPrev {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) : Prop :=
  (∃ res, some res = findPrev tree x ∧ res < x ∧ contains tree res ∧ (∀ i, contains tree i → x ≤ i ∨ i ≤ res))
  ∨ findPrev tree x = none ∧ (∀ i, contains tree i → x ≤ i)
