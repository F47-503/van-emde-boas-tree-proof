import VanEmdeBoas.Operations
import VanEmdeBoas.UtilLemmas

open Classical

def containsNothing {v : Nat} (tree : vEBTree v) : Prop :=
  ∀ i, ¬contains tree i

def correctMin {v : Nat} (tree : vEBTree v) : Prop :=
  match v with
  | 0 =>
    match tree with
    | vEBTree.Leaf _ => True
  | u + 1 =>
    match tree with
    | vEBTree.Node _ summary _ clusters =>
      match summary with
      | none => True
      | some (mi, _) => (∀ i, mi = i ∨ (contains tree i → mi < i)) ∧ ¬contains (clusters (high u mi)) (low u mi)

def correctInvariants {v : Nat} (tree : vEBTree v) : Prop :=
  match v, tree with
  | 0, vEBTree.Leaf _ => True
  | u + 1, vEBTree.Node h summary aux clusters =>
    (correctInvariants aux ∧
    ∀ i, correctInvariants (clusters i)) ∧
    (∀ i, contains aux i ↔ ¬isEmpty (clusters i)) ∧
    match summary with
    | none => isEmpty aux
    | some (_, ma) =>
      correctMin (vEBTree.Node h summary aux clusters) ∧
      ((∀ i, contains (vEBTree.Node h summary aux clusters) i → i ≤ ma) ∧ contains (vEBTree.Node h summary aux clusters) ma)

def recursiveCorrectInvariants {v : Nat} (tree : vEBTree v) : Prop :=
  match v with
  | 0 =>
    match tree with
    | vEBTree.Leaf _ => True
  | _ + 1 =>
    match tree with
    | vEBTree.Node h summary aux clusters =>
      (correctInvariants aux ∧
      ∀ i, correctInvariants (clusters i)) ∧
      (∀ i, contains aux i ↔ ¬isEmpty (clusters i)) ∧
      match summary with
      | none => isEmpty aux
      | some (_, _) =>
        correctMin (vEBTree.Node h summary aux clusters)


def correctAux {v : Nat} (tree : vEBTree v) : Prop :=
  match v with
  | 0 => True
  | _ + 1 =>
    match tree with
    | vEBTree.Node _ _ aux clusters => ∀ i, contains aux i ↔ ¬isEmpty (clusters i)

def correctFindNext {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) : Prop :=
  (∃ res, some res = findNext tree x ∧ x < res ∧ contains tree res ∧ (∀ i, contains tree i → i ≤ x ∨ res ≤ i))
  ∨ findNext tree x = none ∧ (∀ i, contains tree i → i ≤ x)

def correctFindPrev {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) : Prop :=
  (∃ res, some res = findPrev tree x ∧ res < x ∧ contains tree res ∧ (∀ i, contains tree i → x ≤ i ∨ i ≤ res))
  ∨ findPrev tree x = none ∧ (∀ i, contains tree i → x ≤ i)

theorem getMaxReturnsMax (v : Nat) (tree : vEBTree v) (h_inv : correctInvariants tree) (h_non_empty : ¬isEmpty tree):
  (∀ i, contains tree i → i ≤ getMax! v tree h_non_empty) ∧ (contains tree (getMax! v tree h_non_empty)) := by
  match v with
  | 0 =>
    match tree with
    | vEBTree.Leaf f =>
      rw [getMax!]
      rw [isEmpty] at h_non_empty
      rw [not_forall] at h_non_empty
      exact Exists.elim h_non_empty (
        fun x hfx => by
          rw [not_not] at hfx
          by_cases f0 : f 1
          · simp [f0]
            exact And.intro
              (fun i hi => Nat.lt_succ_iff.mp i.isLt)
              (f0)
          · rw [if_neg f0]
            simp at f0
            simp
            have all_0 : ∀ y, f y → y = 0 :=
              fun y hy =>
                Or.elim (zeroOrOneLe y)
                  (fun h₀ => h₀)
                  (fun h₁ => by
                    rw [h₁] at hy
                    rw [hy] at f0
                    contradiction)

            have x1 : x = 0 := all_0 x hfx
            rw [x1] at hfx
            exact And.intro
              all_0
              hfx
      )
  | u + 1 =>
    rw [getMax!.eq_def]
    match tree with
    | vEBTree.Node _ summary aux clusters =>
      match summary with
      | some (mi, ma) =>
        simp
        rw [correctInvariants] at h_inv
        exact h_inv.right.right.right
      | none =>
        rw [isEmpty] at h_non_empty
        simp at h_non_empty

theorem emptyContainsNothing (v : Nat) (tree : vEBTree v) (h_inv : correctInvariants tree) :
  isEmpty tree ↔ containsNothing tree := by
  induction v with
  | zero =>
    rw [isEmpty.eq_def, containsNothing.eq_def]
    match tree with
    | vEBTree.Leaf f =>
      exact Iff.intro
        (fun h_empty =>
          fun i => by
            rw [contains]
            simp
            simp at h_empty
            exact h_empty i)
        (fun not_contains => by
          simp
          exact (fun i => by
            have h_i := not_contains i
            rw [contains] at h_i
            simp at h_i
            exact h_i))
  | succ u ih =>
    exact Iff.intro
      (fun h_empty => by
        rw [containsNothing]
        exact (fun i => by
          rw [contains.eq_def]
          simp
          match tree with
          | vEBTree.Node h_u summary aux clusters =>
            rw [correctInvariants.eq_def] at h_inv
            simp at h_inv
            have h_empty_cluster :=
              ih (clusters (high u i)) (h_inv.left.right (high u i))
            simp
            rw [isEmpty] at h_empty
            simp at h_empty
            rw [containsNothing] at h_empty_cluster
            rw [h_empty] at h_inv
            simp at h_inv
            have aux_contains_nothing := (ih aux h_inv.left.left).mp h_inv.right.right
            rw [containsNothing] at aux_contains_nothing
            simp [h_empty]))
      (fun contains_nothing => by
        match tree with
        | vEBTree.Node h summary aux clusters =>
          rw [isEmpty.eq_def]
          simp
          rw [correctInvariants.eq_def] at h_inv
          simp at h_inv
          match summary with
          | some (mi, ma) =>
            have mi_contains : contains (vEBTree.Node h (some (mi, ma)) aux clusters) mi := by
              rw [contains]
              simp
            rw [containsNothing] at contains_nothing
            exact False.elim ((contains_nothing mi) mi_contains)
          | none => rfl)

theorem containsAux {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) (h_inv : correctInvariants tree) :
  contains tree x → (match v with
    | 0 => True
    | u + 1 =>
      match tree with
      | vEBTree.Node _ summary aux _ => contains aux (high u x) ∨
        match summary with
        | none => False
        | some (mi, _) => mi = x) :=
  match v with
  | 0 => λ_ => by trivial
  | u + 1 =>
    match tree with
    | vEBTree.Node _ summary aux clusters => fun h_contains => by
      simp
      rw [correctInvariants.eq_def] at h_inv
      simp at h_inv
      match summary with
      | none =>
        have h_non_empty : ¬isEmpty (clusters (high u x)):= by
          rw [contains.eq_def] at h_contains
          simp at h_contains
        exact Or.inl ((h_inv.right.left (high u x)).mpr h_non_empty)
      | some (mi, _) =>
        simp
        by_cases h_min : mi = x
        · exact Or.inr h_min
        · have h_non_empty : ¬isEmpty (clusters (high u x)):= by
            rw [contains.eq_def] at h_contains
            simp at h_contains
            simp [h_min] at h_contains
            exact byContradiction (
            fun h_empty => by
              rw [not_not] at h_empty
              have h_contains_nothing := (emptyContainsNothing u (clusters (high u x)) (h_inv.left.right (high u x))).mp h_empty
              rw [containsNothing] at h_contains_nothing
              exact (h_contains_nothing (low u x)) h_contains
          )
          exact Or.inl ((h_inv.right.left (high u x)).mpr h_non_empty)
