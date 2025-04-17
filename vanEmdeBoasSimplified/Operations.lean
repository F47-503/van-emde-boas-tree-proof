import vanEmdeBoasSimplified.Defs

--create empty tree with universe order of v
def createEmpty (v : Nat) : vEBTree v :=
  match v with
  | 0 => vEBTree.Leaf (fun x => False)
  | u + 1 => vEBTree.Node (by linarith) none (createEmpty u) (fun i => createEmpty u)

--check whether the tree is empty (does not have min/max)
def isEmpty {v : Nat} (tree : vEBTree v) : Prop :=
  match tree with
  | vEBTree.Leaf f => (∀ x, ¬f x)
  | vEBTree.Node _ summary _ _ => summary.isNone

--needed for case analysis on emptiness of subtrees
instance {v : Nat} (tree : vEBTree v) : Decidable (isEmpty tree) :=
  match tree with
  | vEBTree.Leaf f =>
    match inferInstanceAs (Decidable (∀ x, ¬f x)) with
      | isTrue h  => isTrue h
      | isFalse h => isFalse h
  | vEBTree.Node _ none _ _ => isTrue rfl
  | vEBTree.Node _ (some _) _ _ => isFalse (fun h => nomatch h)

--get minimum field from tree if it exists
def getMin {v : Nat} (tree : vEBTree v) : Option (Fin (2 ^ 2 ^ v)) :=
  match tree with
  | vEBTree.Leaf f =>
    if f 0
    then
      some 0
    else
      if f 1
      then
        some 1
      else
        none
  | vEBTree.Node _ summary _ _ =>
    match summary with
    | none => none
    | some (mi, _) => mi

--get minimum field from tree under assumption that it exists
def getMin! (v : Nat) (tree : vEBTree v) (h_empty : ¬isEmpty tree): Fin (2 ^ 2 ^ v) :=
  match tree with
  | vEBTree.Leaf f =>
    if f 0
    then
      0
    else
      1
  | vEBTree.Node _ summary _ _ =>
    match summary with
    | none => nomatch h_empty
    | some (mi, _) => mi

--get maximum field from tree if it exists
def getMax {v : Nat} (tree : vEBTree v) : Option (Fin (2 ^ 2 ^ v)) :=
  match tree with
  | vEBTree.Leaf f =>
    if f 1
    then
      some 1
    else
      if f 0
      then
        some 0
      else
        none
  | vEBTree.Node _ summary _ _ =>
    match summary with
    | none => none
    | some (_, ma) => ma

--get maximum field from tree under assumption that it exists
def getMax! (v : Nat) (tree : vEBTree v) (h_empty : ¬isEmpty tree) : Fin (2 ^ 2 ^ v) :=
  match tree with
  | vEBTree.Leaf f =>
    if f 1
    then
      1
    else
      0
  | vEBTree.Node _ summary _ _ =>
    match summary with
    | none => nomatch h_empty
    | some (_, ma) => ma

--check whether a tree contains value
--tree contains value if corresponding cluster contains modulo part of value
def contains {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) : Prop :=
  match v with
  | 0 =>
    match tree with
    | vEBTree.Leaf f => f x
  | u + 1 =>
    match tree with
    | vEBTree.Node _ _ _ clusters =>
      contains (clusters (high u x)) (low u x)

--get minimum from tree without minimum field
def constructiveMin {v : Nat} (tree : vEBTree v) : Option (Fin (2 ^ 2 ^ v)) :=
  match v with
  | 0 =>
    match tree with
    | vEBTree.Leaf f =>
      if f 0
      then
        some 0
      else
        some 1
  | u + 1 =>
    match tree with
    | vEBTree.Node _ _ aux clusters =>
      --empty aux? nothing to do
      if h_aux : isEmpty aux
      then
        none
      --empty minimum cluster of aux? we probably did something wrong
      else if h_cluster : isEmpty (clusters (getMin! u aux h_aux))
        then
          none
        else
        --minimum of minimal cluster should be global minimum
          some (compose u (getMin! u aux h_aux) (getMin! u (clusters (getMin! u aux h_aux)) h_cluster))

--get maximum from tree without maximum field
def constructiveMax {v : Nat} (tree : vEBTree v) : Option (Fin (2 ^ 2 ^ v)) :=
  match v with
  | 0 =>
    match tree with
    | vEBTree.Leaf f =>
      if f 1
      then
        some 1
      else
        some 0
  | u + 1 =>
    match tree with
    | vEBTree.Node _ _ aux clusters =>
      --empty aux? tree is empty, nothing to do
      if h_aux : isEmpty aux
      then
        none
      --max cluster is empty? probably did something wrong
      else if h_cluster : isEmpty (clusters (getMax! u aux h_aux))
        then
          none
        else
        --maximum in max cluster is maximum of the tree
          some (compose u (getMax! u aux h_aux) (getMax! u (clusters (getMax! u aux h_aux)) h_cluster))

--get max and min values from the tree without fields
def recalcSummary {v : Nat} (tree : vEBTree v) : vEBTree v :=
  match v with
  | 0 => tree
  | _ + 1 =>
    match tree with
    | vEBTree.Node h _ aux clusters =>
      vEBTree.Node
        h
        --just need to get min and max without corresponding field usage
        (match (constructiveMin tree, constructiveMax tree) with
          | (some mi, some ma) => some (mi, ma)
          | _ => none
        )
        aux
        clusters

--insert a value to tree
--to insert a value, we insert to cluster and insert to aux index of cluster
def treeInsert {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)): vEBTree v :=
  match v with
  | 0 =>
    match tree with
    | vEBTree.Leaf f => vEBTree.Leaf (fun y => if y = x then True else f y)
  | u + 1 =>
    match tree with
    | vEBTree.Node h _ aux clusters =>
      recalcSummary (
        vEBTree.Node --fix min and max
        h
        (some (x, x)) --we don't care what to put here
        (treeInsert aux (high u x))
        (updateFin clusters (high u x)
          (treeInsert (clusters (high u x)) (low u x))))

--delete a value from tree
--to delete a value, delete from cluster and delete cluster index from aux if became empty
def treeDelete {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) : vEBTree v :=
  match v with
  | 0 =>
    match tree with
    | vEBTree.Leaf f => vEBTree.Leaf (fun y => if y = x then False else f y)
  | u + 1 =>
    match tree with
    | vEBTree.Node h summary aux clusters =>
      recalcSummary --fix min and max
        (vEBTree.Node
          h
          summary --might keep summary, recalcSummary fixes it
          (if isEmpty (treeDelete (clusters (high u x)) (low u x))
            then
              treeDelete aux (high u x)
            else aux)
          (updateFin clusters (high u x)
            (treeDelete (clusters (high u x)) (low u x))))

--find next value in tree after x
def findNext {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) : Option (Fin (2 ^ 2 ^ v)) :=
  match v with
  | 0 =>
    match tree with
    | vEBTree.Leaf f =>
        if x = 0 ∧ f 1
        then
          some 1
        else
          none
  | u + 1 =>
    match tree with
    | vEBTree.Node _ _ aux clusters =>
      --if cluster with x is empty, take lower bound in aux
      if h_empty : isEmpty (clusters (high u x))
      then
        match findNext aux (high u x) with
        --if next does not exist, x is max
        | none => none
        | some res =>
          --something is wrong, aux contains non-empty clusters
          if h_cluster_empty : isEmpty (clusters res)
          then
            none
          else
            some (compose u res (getMin! u (clusters res) h_cluster_empty))
      else
        --try to take max in cluster
        if low u x < getMax! u (clusters (high u x)) h_empty
        then
          match findNext (clusters (high u x)) (low u x) with
          | none => none
          | some res => some (compose u (high u x) res)
        else
          match findNext aux (high u x) with
          | none => none
          | some res =>
            if h_cluster_empty : isEmpty (clusters res)
            then
              none
            else
              some (compose u res (getMin! u (clusters res) h_cluster_empty))

--find previous value in tree before x
def findPrev {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) : Option (Fin (2 ^ 2 ^ v)) :=
  match v with
  | 0 =>
    match tree with
    | vEBTree.Leaf f =>
      if x = 1 ∧ f 0
      then
        some 0
      else
        none
  | u + 1 =>
    match tree with
    | vEBTree.Node _ _ aux clusters =>
      --if cluster with x is empty, take upper bound in aux
      if h_empty : isEmpty (clusters (high u x))
      then
        match findPrev aux (high u x) with
        --if previous does not exist, x is min
        | none => none
        | some res =>
          if h_cluster_empty : isEmpty (clusters res)
          then
            --something is wrong, aux contains non-empty clusters
            none
          else
            some (compose u res (getMax! u (clusters res) h_cluster_empty))
      else
        --try to take min in cluster
        if getMin! u (clusters (high u x)) h_empty < low u x
        then
          match findPrev (clusters (high u x)) (low u x) with
          | none => none
          | some res => some (compose u (high u x) res)
        else
          match findPrev aux (high u x) with
          | none => none
          | some res =>
            if h_cluster_empty : isEmpty (clusters res)
            then
              none
            else
              some (compose u res (getMax! u (clusters res) h_cluster_empty))
