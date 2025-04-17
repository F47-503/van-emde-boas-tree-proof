import Mathlib.Tactic
import vanEmdeBoasSimplified.Defs
import vanEmdeBoasSimplified.UtilLemmas
import vanEmdeBoasSimplified.Operations
import vanEmdeBoasSimplified.Invariants

open Classical

--minimum returns minimum under invariants
--needed for consistency between v = 0, v > 0
theorem getMinReturnsMin (v : Nat) (tree : vEBTree v) (h_summary : correctSummary tree) (h_aux : correctAux tree) (h_non_empty : ¬isEmpty tree):
  (contains tree (getMin! v tree h_non_empty)) ∧ (∀ i, contains tree i → getMin! v tree h_non_empty ≤ i) := by
  match v with
  | 0 =>
    match tree with
    | vEBTree.Leaf f =>
      rw [getMin!]
      rw [isEmpty] at h_non_empty
      rw [not_forall] at h_non_empty
      exact Exists.elim h_non_empty (
        fun x hfx => by
          rw [not_not] at hfx
          by_cases f0 : f 0
          · simp [f0]
            exact f0
          · rw [if_neg f0]
            simp at f0
            simp
            have x_not_0 : ∀ y, f y → y.val ≠ 0 :=
              fun y hy =>
                byContradiction (
                  fun y0 => by
                    simp at y0
                    rw [y0] at hy
                    rw [f0] at hy
                    contradiction
                )

            have x1 : x = 1 := le_antisymm
              (Nat.le_pred_of_lt x.isLt)
              (Nat.pos_of_ne_zero (x_not_0 x hfx))
            rw [x1] at hfx
            exact And.intro
              hfx
              (fun i h_i => Nat.pos_of_ne_zero (x_not_0 i h_i))
      )
  | u + 1 =>
    rw [getMin!.eq_def]
    match tree with
    | vEBTree.Node _ summary aux clusters =>
      match summary with
      | some (mi, ma) =>
        simp
        rw [correctSummary] at h_summary
        exact h_summary.right.left
      | none =>
        rw [isEmpty] at h_non_empty
        simp at h_non_empty


--maximum returns maximum under invariants
--needed for consistency between v = 0, v > 0
theorem getMaxReturnsMax (v : Nat) (tree : vEBTree v) (h_summary : correctSummary tree) (h_aux : correctAux tree) (h_non_empty : ¬isEmpty tree):
  (contains tree (getMax! v tree h_non_empty)) ∧ (∀ i, contains tree i → i ≤ getMax! v tree h_non_empty) := by
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
              (f0)
              (fun i hi => Nat.lt_succ_iff.mp i.isLt)
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
              hfx
              all_0
      )
  | u + 1 =>
    rw [getMax!.eq_def]
    match tree with
    | vEBTree.Node _ summary aux clusters =>
      match summary with
      | some (mi, ma) =>
        simp
        rw [correctSummary] at h_summary
        exact h_summary.right.right
      | none =>
        rw [isEmpty] at h_non_empty
        simp at h_non_empty

--under invariants tree is empty equivalent to tree contains nothing
theorem emptyContainsNothing (v : Nat) (tree : vEBTree v) (h_aux : correctAux tree) (h_summary : correctSummary tree) :
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
            rw [correctAux] at h_aux
            have h_empty_cluster :=
              ih (clusters (high u i)) (h_aux.right.left (high u i)) (h_summary.left.right (high u i))
            simp
            rw [correctSummary.eq_def] at h_summary
            rw [isEmpty] at h_empty
            simp at h_empty
            rw [containsNothing] at h_empty_cluster
            rw [h_empty] at h_summary
            simp at h_summary
            have aux_contains_nothing := (ih aux h_aux.left h_summary.left.left).mp h_summary.right.right
            rw [containsNothing] at aux_contains_nothing
            exact (h_empty_cluster.mp ((h_aux.right.right (high u i)).mpr (aux_contains_nothing (high u i)))) (low u i)))
      (fun contains_nothing => by
        match tree with
        | vEBTree.Node h summary aux clusters =>
          rw [isEmpty.eq_def]
          simp
          rw [correctSummary.eq_def] at h_summary
          simp at h_summary
          match summary with
          | some (mi, ma) =>
            simp at h_summary
            rw [containsNothing] at contains_nothing
            exact False.elim ((contains_nothing mi) (h_summary.right.left.left))
          | none => rfl)

--under recursive part of summary if tree contains x then aux contains index of cluster
theorem containsAux {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) (h_aux : correctAux tree) (h_summary : recursiveCorrectSummary tree):
  contains tree x → (match v with
    | 0 => True
    | u + 1 =>
      match tree with
      | vEBTree.Node _ _ aux _ => contains aux (high u x)) :=
  match v with
  | 0 => λ_ => by trivial
  | u + 1 =>
    match tree with
    | vEBTree.Node _ _ aux clusters => fun h_contains => by
      simp
      rw [correctAux] at h_aux
      simp at h_aux
      rw [recursiveCorrectSummary] at h_summary
      simp at h_summary
      have h_non_empty : ¬isEmpty (clusters (high u x)) := by
        rw [contains] at h_contains
        exact byContradiction (
          fun h_empty => by
            rw [not_not] at h_empty
            have h_contains_nothing := (emptyContainsNothing u (clusters (high u x)) (h_aux.right.left (high u x)) (h_summary.right (high u x))).mp h_empty
            rw [containsNothing] at h_contains_nothing
            exact (h_contains_nothing (low u x)) h_contains
        )
      exact not_not.mp ((not_iff_not.mpr (h_aux.right.right (high u x))).mp h_non_empty)

--constructive minimum is minimum
theorem constructiveMinIsMin {v : Nat} (tree : vEBTree v) (h_aux : correctAux tree) (h_summary : recursiveCorrectSummary tree) (h_contains : ¬containsNothing tree):
  ∃ mi, constructiveMin tree = some mi ∧ contains tree mi ∧ (∀ i, contains tree i → mi ≤ i) := by
    match v with
    | 0 =>
      match tree with
      | vEBTree.Leaf f =>
        rw [constructiveMin]
        by_cases h₀ : f 0
        · rw [if_pos h₀]
          exact Exists.intro 0 (
            And.intro
              (rfl)
              (And.intro
                (by trivial)
                (fun i hi => Fin.zero_le i))
          )
        · rw [if_neg h₀]
          exact Exists.intro 1 (
            And.intro
              (rfl)
              (And.intro
                (by
                  rw [containsNothing] at h_contains
                  simp at h_contains
                  exact Exists.elim h_contains
                    (fun x hx => Or.elim (zeroOrOneLe x)
                      (fun hx₀ => by
                        rw [hx₀] at hx
                        contradiction)
                      (fun hx₁ => by
                        rw [contains]
                        rw [hx₁] at hx
                        exact hx)))
                (fun i h_i => Or.elim (zeroOrOneLe i)
                  (fun hi₀ => by
                    rw [contains] at h_i
                    rw [hi₀] at h_i
                    contradiction)
                  (fun hi₁ => by
                    rw [hi₁])))
          )
    | u + 1 =>
      match tree with
      | vEBTree.Node h summary aux clusters =>
        rw [constructiveMin]
        rw [correctAux] at h_aux
        rw [recursiveCorrectSummary] at h_summary
        rw [containsNothing] at h_contains
        simp at h_contains
        exact Exists.elim h_contains
          (fun x hx => by
            have aux_contains : contains aux (high u x) :=
              containsAux (vEBTree.Node h summary aux clusters) x h_aux h_summary hx
            have aux_non_empty : ¬isEmpty aux :=
              byContradiction (fun aux_empty => by
                have aux_contains_nothing := (emptyContainsNothing u aux h_aux.left h_summary.left).mp (not_not.mp aux_empty)
                rw [containsNothing] at aux_contains_nothing
                exact (aux_contains_nothing (high u x)) aux_contains
              )
            have h_min_aux := getMinReturnsMin u aux h_summary.left h_aux.left aux_non_empty
            have cluster_non_empty := (not_iff_not.mpr (h_aux.right.right (getMin! u aux aux_non_empty))).mpr (not_not.mpr h_min_aux.left)
            have h_min_cluster := getMinReturnsMin u (clusters (getMin! u aux aux_non_empty)) (h_summary.right (getMin! u aux aux_non_empty)) (h_aux.right.left (getMin! u aux aux_non_empty)) cluster_non_empty
            simp [aux_non_empty]
            exact Exists.intro cluster_non_empty
              (And.intro
                (by
                  rw [contains]
                  simp
                  rw [composeCorrectHigh, composeCorrectLow]
                  exact h_min_cluster.left)
                (fun i h_i => by
                  rw [contains] at h_i
                  have aux_i := containsAux (vEBTree.Node h summary aux clusters) i h_aux h_summary h_i
                  simp at aux_i
                  have aux_le := h_min_aux.right (high u i) aux_i
                  rw [transformKeysLe u]
                  rw [composeCorrectHigh, composeCorrectLow]
                  by_cases aux_eq : getMin! u aux aux_non_empty = high u i
                  · rw [←aux_eq] at h_i
                    exact Or.inr (And.intro
                      aux_eq
                      ((h_min_cluster.right (low u i)) h_i))
                  · rw [Fin.ext_iff] at aux_eq
                    exact Or.inl (Nat.lt_of_le_of_ne aux_le aux_eq))))

--constructive maximum is maximum
theorem constructiveMaxIsMax {v : Nat} (tree : vEBTree v) (h_aux : correctAux tree) (h_summary : recursiveCorrectSummary tree) (h_contains : ¬containsNothing tree):
  ∃ ma, constructiveMax tree = some ma ∧ contains tree ma ∧ (∀ i, contains tree i → i ≤ ma) := by
    match v with
    | 0 =>
      match tree with
      | vEBTree.Leaf f =>
        rw [constructiveMax]
        by_cases h₀ : f 1
        · rw [if_pos h₀]
          exact Exists.intro 1 (
            And.intro
              (rfl)
              (And.intro
                (by trivial)
                (fun i hi => Nat.lt_succ_iff.mp i.isLt))
          )
        · rw [if_neg h₀]
          exact Exists.intro 0 (
            And.intro
              (rfl)
              (And.intro
                (by
                  rw [containsNothing] at h_contains
                  simp at h_contains
                  exact Exists.elim h_contains
                    (fun x hx => Or.elim (zeroOrOneLe x)
                      (fun hx₀ => by
                        rw [hx₀] at hx
                        exact hx)
                      (fun hx₁ => by
                        rw [contains]
                        rw [hx₁] at hx
                        contradiction)))
                (fun i h_i => Or.elim (zeroOrOneLe i)
                  (fun hi₁ => by
                    rw [hi₁])
                  (fun hi₀ => by
                    rw [contains] at h_i
                    rw [hi₀] at h_i
                    contradiction))))
    | u + 1 =>
      match tree with
      | vEBTree.Node h summary aux clusters =>
        rw [constructiveMax]
        rw [correctAux] at h_aux
        rw [recursiveCorrectSummary] at h_summary
        rw [containsNothing] at h_contains
        simp at h_contains
        exact Exists.elim h_contains
          (fun x hx => by
            have aux_contains : contains aux (high u x) :=
              containsAux (vEBTree.Node h summary aux clusters) x h_aux h_summary hx
            have aux_non_empty : ¬isEmpty aux :=
              byContradiction (fun aux_empty => by
                have aux_contains_nothing := (emptyContainsNothing u aux h_aux.left h_summary.left).mp (not_not.mp aux_empty)
                rw [containsNothing] at aux_contains_nothing
                exact (aux_contains_nothing (high u x)) aux_contains
              )
            have h_max_aux := getMaxReturnsMax u aux h_summary.left h_aux.left aux_non_empty
            have cluster_non_empty := (not_iff_not.mpr (h_aux.right.right (getMax! u aux aux_non_empty))).mpr (not_not.mpr h_max_aux.left)
            have h_max_cluster := getMaxReturnsMax u (clusters (getMax! u aux aux_non_empty)) (h_summary.right (getMax! u aux aux_non_empty)) (h_aux.right.left (getMax! u aux aux_non_empty)) cluster_non_empty
            simp [aux_non_empty]
            exact Exists.intro cluster_non_empty
              (And.intro
                (by
                  rw [contains]
                  simp
                  rw [composeCorrectHigh, composeCorrectLow]
                  exact h_max_cluster.left)
                (fun i h_i => by
                  rw [contains] at h_i
                  have aux_i := containsAux (vEBTree.Node h summary aux clusters) i h_aux h_summary h_i
                  simp at aux_i
                  have aux_le := h_max_aux.right (high u i) aux_i
                  rw [transformKeysLe u]
                  rw [composeCorrectHigh, composeCorrectLow]
                  by_cases aux_eq : high u i = getMax! u aux aux_non_empty
                  · rw [aux_eq] at h_i
                    exact Or.inr (And.intro
                      aux_eq
                      ((h_max_cluster.right (low u i)) h_i))
                  · rw [Fin.ext_iff] at aux_eq
                    exact Or.inl (Nat.lt_of_le_of_ne aux_le aux_eq))))

--under recursive part of summary,
--we can recalculate minimum and maximum with constructive min/constructive max
theorem recalcCorrectSummary (v : Nat) (tree : vEBTree v) (h_aux : correctAux tree) (h_summary : recursiveCorrectSummary tree) :
  correctSummary (recalcSummary tree) :=
  match v with
  | 0 => by
    rw [recalcSummary]
    rw [correctSummary.eq_def]
    trivial
  | u + 1 =>
    match tree with
    | vEBTree.Node h summary aux clusters => by
      rw [recalcSummary]
      rw [correctSummary.eq_def]
      simp
      exact And.intro
        h_summary
        (by
          by_cases contains_nothing : containsNothing (vEBTree.Node h summary aux clusters)
          · rw [constructiveMax, constructiveMin]
            rw [recursiveCorrectSummary] at h_summary
            have aux_contains_nothing : containsNothing aux := byContradiction (
              fun aux_contains => by
                rw [containsNothing] at aux_contains
                simp at aux_contains
                rw [containsNothing] at contains_nothing
                exact Exists.elim aux_contains (
                  fun x hx => by
                    rw [correctAux] at h_aux
                    have non_empty_cluster := (not_iff_not.mpr (h_aux.right.right x)).mpr (not_not.mpr hx)
                    have cluster_contains := (not_iff_not.mpr (emptyContainsNothing u (clusters x) (h_aux.right.left x) (h_summary.right x))).mp non_empty_cluster
                    rw [containsNothing] at cluster_contains
                    simp at cluster_contains
                    exact Exists.elim cluster_contains (
                      fun y hy => by
                        have not_contains_compose := contains_nothing (compose u x y)
                        rw [contains] at not_contains_compose
                        rw [composeCorrectHigh, composeCorrectLow] at not_contains_compose
                        exact False.elim (not_contains_compose hy)
                    )
                )
            )
            have aux_empty := (emptyContainsNothing u aux h_aux.left h_summary.left).mpr aux_contains_nothing
            simp [aux_empty]
            exact contains_nothing
          · have h_min_construct := constructiveMinIsMin (vEBTree.Node h summary aux clusters) h_aux h_summary contains_nothing
            have h_max_construct := constructiveMaxIsMax (vEBTree.Node h summary aux clusters) h_aux h_summary contains_nothing
            obtain ⟨mi, min_val, h_min⟩ := h_min_construct
            rw [min_val]
            obtain ⟨ma, max_val, h_max⟩ := h_max_construct
            rw [max_val]
            exact And.intro
              h_min
              h_max)

theorem createEmptyIsEmpty (v : Nat) : isEmpty (createEmpty v) := by
  match v with
  | 0 =>
    rw [createEmpty.eq_def]
    rw [isEmpty]
    simp
  | u + 1 =>
    rw [createEmpty.eq_def]
    rw [isEmpty]
    simp

theorem createEmptyNotContains (v : Nat) :
  ∀ i : Fin (2 ^ 2 ^ v), ¬contains (createEmpty v) i := by
  induction v with
  | zero =>
    exact (fun i => by
      rw [contains.eq_def]
      rw [createEmpty]
      simp)
  | succ u ih =>
    exact (fun i => by
      rw [contains.eq_def]
      rw [createEmpty.eq_def]
      simp
      exact ih (low u i))

theorem createCorrectAux (v : Nat) : correctAux (createEmpty v) := by
  induction v with
  | zero =>
    rw [createEmpty]
    rw [correctAux]
    simp
  | succ u ih =>
    rw [createEmpty]
    rw [correctAux]
    simp
    exact And.intro
      (ih)
      (fun i =>
        Iff.intro
          (fun _ => by
            exact (fun h_contains =>
                ((createEmptyNotContains u) i) h_contains))
          (fun _ => createEmptyIsEmpty u))

theorem insertContainsNew {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)):
  contains (treeInsert tree x) x := by
  induction v with
  | zero =>
    match tree with
    | vEBTree.Leaf _ =>
      rw [contains.eq_def]
      rw [treeInsert]
      simp
  | succ u ih =>
    match tree with
    | vEBTree.Node _ _ aux clusters =>
      rw [contains.eq_def]
      rw [treeInsert.eq_def]
      simp
      rw [recalcSummary.eq_def]
      simp
      rw [updateFin]
      simp
      exact (ih
        (clusters (high u x))
        (low u x))

--for each y except for x,
--y was in tree iff y is in tree after insertion
theorem insertContainsOld {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)):
  ∀ i, i ≠ x → (contains (treeInsert tree x) i ↔ contains tree i) := by
    induction v with
    | zero =>
      exact (fun i =>
        fun h_not_x =>
          match tree with
          | vEBTree.Leaf f => by
            rw [contains.eq_def]
            rw [treeInsert.eq_def]
            rw [contains.eq_def]
            simp
            exact (fun h_x => absurd h_x h_not_x))
    | succ u ih =>
      exact (fun i =>
        fun h_not_x =>
          match tree with
          | vEBTree.Node _ _ aux clusters => by
            rw [contains.eq_def]
            rw [treeInsert.eq_def]
            rw [contains.eq_def]
            simp
            rw [recalcSummary.eq_def]
            simp
            rw [updateFin]
            by_cases h_ix : high u i = high u x
            · rw [if_pos h_ix]
              rw [h_ix]
              have h_neq : low u i ≠ low u x :=
                fun h_eq => absurd h_not_x (not_not.mpr (eqDivMod u i x h_ix h_eq))
              exact ((ih (clusters (high u x)) (low u x)) (low u i)) h_neq
            · rw [if_neg h_ix])

--insert preserves both invariants
theorem insertCorrectInvariants (v : Nat) (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) (h_aux : correctAux tree) (h_summary : correctSummary tree):
  correctAux (treeInsert tree x) ∧ correctSummary (treeInsert tree x) := by
  induction v with
  | zero =>
    exact And.intro
      (by
        rw [correctAux]
        simp)
      (by
        rw [correctSummary.eq_def]
        rw [treeInsert.eq_def]
        match tree with
        | vEBTree.Leaf _ => simp)
  | succ u ih =>
    have aux_proof : correctAux (treeInsert tree x) := by
        rw [treeInsert.eq_def]
        match tree with
        | vEBTree.Node _ _ aux clusters =>
          rw [correctAux] at h_aux
          rw [correctSummary.eq_def] at h_summary
          have h_cluster := ih (clusters (high u x)) (low u x) (h_aux.right.left (high u x))
                    (h_summary.left.right (high u x))
          exact And.intro
            ((ih aux (high u x)) h_aux.left h_summary.left.left).left
            (And.intro
              (fun i => by
                rw [updateFin]
                split
                case isTrue =>
                  exact
                    (h_cluster).left
                case isFalse => exact h_aux.right.left i)
              (fun i => by
                rw [updateFin]
                split
                case isTrue hi =>
                  exact Iff.intro
                    (fun h_empty =>
                      have contains_nothing := emptyContainsNothing
                        u
                        (treeInsert (clusters (high u x)) (low u x))
                        h_cluster.left
                        h_cluster.right
                      False.elim (
                        (contains_nothing.mp h_empty) (low u x)
                        (insertContainsNew (clusters (high u x)) (low u x))))
                    (fun h_not_contains => by
                      rw [hi] at h_not_contains
                      exact False.elim (h_not_contains (insertContainsNew
                        aux
                        (high u x))))
                case isFalse h_non_empty =>
                  have h₂ := Iff.not (Iff.comm.mp ((insertContainsOld aux (high u x) i) h_non_empty))
                  have h₃ := (h_aux.right.right i)
                  exact Iff.trans h₃ h₂))
    exact And.intro
      aux_proof
      (by
        match tree with
        | vEBTree.Node h summary aux clusters =>
          rw [treeInsert]
          have h_summary_rec : recursiveCorrectSummary (treeInsert (vEBTree.Node h summary aux clusters) x) := by
            rw [recursiveCorrectSummary.eq_def]
            rw [treeInsert]
            rw [recalcSummary]
            rw [correctAux] at h_aux
            rw [correctSummary.eq_def] at h_summary
            simp at h_summary
            simp
            exact And.intro
              (ih aux (high u x) h_aux.left h_summary.left.left).right
              (fun i => by
                rw [updateFin]
                by_cases h_i : i = high u x
                · simp [h_i]
                  exact (ih (clusters (high u x)) (low u x)
                    (h_aux.right.left (high u x))
                    (h_summary.left.right (high u x))).right
                · simp [h_i]
                  exact h_summary.left.right i)
          exact recalcCorrectSummary (u + 1) (vEBTree.Node h (some (x, x)) (treeInsert aux (high u x)) (updateFin clusters (high u x) (treeInsert (clusters (high u x)) (low u x))))
            aux_proof
            h_summary_rec)

--if we delete x, tree does not contain x
theorem deleteNotContainsNew {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)):
  ¬contains (treeDelete tree x) x := by
  induction v with
  | zero =>
    match tree with
    | vEBTree.Leaf _ =>
      rw [contains.eq_def]
      rw [treeDelete]
      simp
  | succ u ih =>
    match tree with
    | vEBTree.Node _ _ aux clusters =>
      rw [contains.eq_def]
      rw [treeDelete.eq_def]
      simp
      rw [recalcSummary]
      simp
      rw [updateFin]
      simp
      exact (ih
        (clusters (high u x))
        (low u x))

--for each y except for x,
--y was in tree iff y is in tree after deletion
theorem deleteContainsOld {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)):
  ∀ i, i ≠ x → (contains (treeDelete tree x) i ↔ contains tree i) := by
    induction v with
    | zero =>
      exact (fun i =>
        fun h_not_x =>
          match tree with
          | vEBTree.Leaf f => by
            rw [contains.eq_def]
            rw [treeDelete.eq_def]
            rw [contains.eq_def]
            simp
            exact (fun h_x => h_not_x))
    | succ u ih =>
      exact (fun i =>
        fun h_not_x =>
          match tree with
          | vEBTree.Node _ _ aux clusters => by
            rw [contains.eq_def]
            rw [treeDelete.eq_def]
            rw [contains.eq_def]
            simp
            rw [recalcSummary]
            simp
            rw [updateFin]
            by_cases h_ix : high u i = high u x
            · rw [if_pos h_ix]
              rw [h_ix]
              have h_neq : low u i ≠ low u x :=
                fun h_eq => absurd h_not_x (not_not.mpr (eqDivMod u i x h_ix h_eq))
              exact ((ih (clusters (high u x)) (low u x)) (low u i)) h_neq
            · rw [if_neg h_ix])

theorem createEmptyContainsNothing (v : Nat) :
  containsNothing (createEmpty v) :=
    createEmptyNotContains v

theorem createEmptycorrectSummary (v : Nat) : correctSummary (createEmpty v) := by
  induction v with
  | zero =>
    rw [createEmpty.eq_def]
    rw [correctSummary.eq_def]
    simp
  | succ u ih =>
    rw[correctSummary.eq_def]
    have h := createEmptyContainsNothing (u + 1)
    rw [createEmpty.eq_def]
    rw [createEmpty.eq_def] at h
    simp
    exact And.intro ih (And.intro h (createEmptyIsEmpty u))

--delete preserves both invariants
theorem deleteCorrectInvariants (v : Nat) (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) (h_aux : correctAux tree) (h_summary : correctSummary tree) :
  correctAux (treeDelete tree x) ∧ correctSummary (treeDelete tree x) := by
  induction v with
  | zero =>
    exact And.intro
      (by
        rw [correctAux]
        simp)
      (by
        match tree with
        | vEBTree.Leaf f =>
          rw [correctSummary.eq_def]
          rw [treeDelete]
          simp)
  | succ u ih =>
    have delete_aux_proof : correctAux (treeDelete tree x) := by
      rw [treeDelete.eq_def]
      match tree with
      | vEBTree.Node _ _ aux clusters =>
        rw [correctAux] at h_aux
        rw [correctSummary.eq_def] at h_summary
        simp at h_summary
        exact And.intro
          (by
            by_cases h_empty_res : isEmpty (treeDelete (clusters (high u x)) (low u x))
            · rw [if_pos h_empty_res]
              exact ((ih aux (high u x)) h_aux.left h_summary.left.left).left
            · rw [if_neg h_empty_res]
              exact h_aux.left)
          (And.intro
            (fun i => by
              rw [updateFin]
              split
              case isTrue =>
                exact
                  (ih (clusters (high u x)) (low u x) (h_aux.right.left (high u x))
                    (h_summary.left.right (high u x))).left
              case isFalse => exact h_aux.right.left i)
            (fun i => by
              rw [updateFin]
              split
              case isTrue hi =>
                rw [hi]
                by_cases h_empty_res : isEmpty (treeDelete (clusters (high u x)) (low u x))
                · rw [if_pos h_empty_res]
                  have h_no_high := deleteNotContainsNew aux (high u x)
                  exact Iff.intro (λ _ => h_no_high) (λ _ => h_empty_res)
                · rw [if_neg h_empty_res]
                  have h_cluster := ih (clusters (high u x)) (low u x) (h_aux.right.left (high u x))
                    (h_summary.left.right (high u x))
                  have non_empty : ¬isEmpty (clusters (high u x)) := by
                    have h_invariants := emptyContainsNothing u (treeDelete (clusters (high u x)) (low u x)) h_cluster.left h_cluster.right
                    have h_invariants_old := emptyContainsNothing u (clusters (high u x)) (h_aux.right.left (high u x)) (h_summary.left.right (high u x))
                    have res_contains_nothing := (not_iff_not.mpr (h_invariants)).mp h_empty_res
                    rw [containsNothing] at res_contains_nothing
                    simp at res_contains_nothing
                    exact Exists.elim res_contains_nothing (
                      fun y hy =>
                        have not_y : y ≠ (low u x) := byContradiction (
                          fun y_eq => by
                            simp at y_eq
                            rw [y_eq] at hy
                            exact (deleteNotContainsNew (clusters (high u x)) (low u x)) hy
                        )
                        have contains_y := (deleteContainsOld (clusters (high u x)) (low u x) y not_y).mp hy
                        (not_iff_not.mpr h_invariants_old).mpr
                          (by
                            rw [containsNothing]
                            simp
                            exact Exists.intro y contains_y)
                    )
                  have from_aux := h_aux.right.right (high u x)
                  exact Iff.trans
                    (Iff.intro
                      (λ _ => False.elim (h_empty_res (by assumption)))
                      (λ _ => False.elim (non_empty (by assumption))))
                    from_aux
              case isFalse h_non_empty =>
                have h₂ := Iff.not (Iff.comm.mp ((deleteContainsOld aux (high u x) i) h_non_empty))
                have h₃ := (h_aux.right.right i)
                by_cases h_empty_res : isEmpty (treeDelete (clusters (high u x)) (low u x))
                · rw [if_pos h_empty_res]
                  exact Iff.trans h₃ h₂
                · rw [if_neg h_empty_res]
                  exact h₃))
    exact And.intro
      delete_aux_proof
      (by
        match tree with
        | vEBTree.Node h summary aux clusters =>
          rw [treeDelete]
          rw [treeDelete] at delete_aux_proof
          have delete_summary_clusters := (ih (clusters (high u x)) (low u x) (h_aux.right.left (high u x)) (h_summary.left.right (high u x))).right
          have delete_summary_aux := (ih aux (high u x) h_aux.left h_summary.left.left).right
          by_cases h_cluster_empty : isEmpty (treeDelete (clusters (high u x)) (low u x))
          · simp [h_cluster_empty]
            simp [h_cluster_empty] at delete_aux_proof
            exact recalcCorrectSummary (u + 1) (vEBTree.Node h summary (treeDelete aux (high u x)) (updateFin clusters (high u x) (treeDelete (clusters (high u x)) (low u x))))
              (delete_aux_proof)
              (by
                rw [recursiveCorrectSummary]
                exact And.intro
                  delete_summary_aux
                  (fun i => by
                    rw [updateFin]
                    by_cases h_i : i = high u x
                    · simp [h_i]
                      exact delete_summary_clusters
                    · simp [h_i]
                      exact h_summary.left.right i))
          · simp [h_cluster_empty]
            simp [h_cluster_empty] at delete_aux_proof
            exact recalcCorrectSummary (u + 1) (vEBTree.Node h summary aux (updateFin clusters (high u x) (treeDelete (clusters (high u x)) (low u x))))
              (delete_aux_proof)
              (by
                rw [recursiveCorrectSummary]
                exact And.intro
                  h_summary.left.left
                  (fun i => by
                    rw [updateFin]
                    by_cases h_i : i = high u x
                    · simp [h_i]
                      exact delete_summary_clusters
                    · simp [h_i]
                      exact h_summary.left.right i)))

--createEmpty ensures both invariants
theorem createCorrectInvariants (v : Nat) : correctAux (createEmpty v) ∧ correctSummary (createEmpty v) :=
  And.intro (createCorrectAux v) (createEmptycorrectSummary v)
