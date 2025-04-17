import VanEmdeBoas.Defs

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

def isSingleton {v : Nat} (tree : vEBTree v) : Prop :=
  match tree with
  | vEBTree.Leaf f => ∃ x, (∀ y, f y ↔ x = y)
  | vEBTree.Node _ summary _ _ =>
    match summary with
    | some (mi, ma) => mi == ma
    | none => False

--needed for case analysis on emptiness of subtrees
instance {v : Nat} (tree : vEBTree v) : Decidable (isEmpty tree) :=
  match tree with
  | vEBTree.Leaf f =>
    match inferInstanceAs (Decidable (∀ x, ¬f x)) with
      | isTrue h  => isTrue h
      | isFalse h => isFalse h
  | vEBTree.Node _ none _ _ => isTrue rfl
  | vEBTree.Node _ (some _) _ _ => isFalse (fun h => nomatch h)

instance {v : Nat} (tree : vEBTree v) : Decidable (isSingleton tree) :=
  match tree with
  | vEBTree.Leaf f =>
    match inferInstanceAs (Decidable (∃ x, (∀ y, f y ↔ x = y))) with
      | isTrue h  => isTrue h
      | isFalse h => isFalse h
  | vEBTree.Node _ none _ _ => isFalse (fun h => nomatch h)
  | vEBTree.Node _ (some (mi, ma)) _ _ =>
    if h : mi = ma
    then
      isTrue (by
        simp [isSingleton]
        exact h)
    else
      isFalse (by
        simp [isSingleton]
        exact h)

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
    | vEBTree.Node _ summary _ clusters =>
      match summary with
      | some (mi, _) => if mi = x then True else contains (clusters (high u x)) (low u x)
      | none => False

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
    | vEBTree.Node h summary aux clusters =>
      match summary with
      | some (mi, _) =>
        vEBTree.Node
          h
          --just need to get min and max without corresponding field usage
          (match constructiveMax tree with
            | some ma => some (mi, ma)
            | _ => some (mi, mi)
          )
          aux
          clusters
      | none =>
        vEBTree.Node
          h
          none
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
    | vEBTree.Node h summary aux clusters =>
      match summary with
      | some (mi, ma) =>
        if mi = x
        then
          tree
        else
          if x < mi
          then
            vEBTree.Node
              h
              (x, max ma x)
              (if isEmpty (clusters (high u mi))
              then
                treeInsert aux (high u mi)
              else
                aux)
              (updateFin (clusters) (high u mi)
                (treeInsert (clusters (high u mi)) (low u mi)))
          else
            vEBTree.Node
              h
              (mi, max ma x)
              (if isEmpty (clusters (high u x))
              then
                treeInsert aux (high u x)
              else
                aux)
              (updateFin (clusters) (high u x)
                (treeInsert (clusters (high u x)) (low u x)))
      | none =>
        vEBTree.Node
          h
          (some (x, x))
          aux
          clusters
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
      match summary with
      | some (mi, ma) =>
        if  mi = x
        then
          if ma = mi
          then
            vEBTree.Node
              h
              none
              aux
              clusters
          else
            match constructiveMin tree with
            --impossible case
            | none =>
              vEBTree.Node
                h
                none
                aux
                clusters
            --delete minimum in underlying structure instead
            | some res =>
              recalcSummary (
                vEBTree.Node
                  h
                  (some (res, ma))
                  (if isEmpty (treeDelete (clusters (high u res)) (low u res))
                  then
                    treeDelete aux (high u res)
                  else
                    aux)
                  (updateFin clusters (high u res) (treeDelete (clusters (high u res)) (low u res))))
        else
          recalcSummary (
            vEBTree.Node
              h
              (some (mi, ma))
              (if isEmpty (treeDelete (clusters (high u x)) (low u x))
              then
                treeDelete aux (high u x)
              else
                aux)
              (updateFin clusters (high u x) (treeDelete (clusters (high u x)) (low u x))))
      | none => tree

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
      if h_empty : isEmpty (clusters (high u x))
      then
        match findPrev aux (high u x) with
        | none => none
        | some res =>
          if h_cluster_empty : isEmpty (clusters res)
          then
            none
          else
            some (compose u res (getMax! u (clusters res) h_cluster_empty))
      else
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
