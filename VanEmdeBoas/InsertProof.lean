import Mathlib.Tactic
import VanEmdeBoas.Defs
import VanEmdeBoas.UtilLemmas
import VanEmdeBoas.Operations
import VanEmdeBoas.Invariants

open Classical

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
      simp)


theorem createCorrectInvariants (v : Nat) : correctInvariants (createEmpty v) := by
  induction v with
  | zero =>
    rw [createEmpty]
    rw [correctInvariants]
    simp
  | succ u ih =>
    rw [createEmpty]
    rw [correctInvariants]
    simp
    exact And.intro
      ih
      (And.intro
        (fun i =>
          have contains_nothing := createEmptyNotContains u
          Iff.intro
            (fun empty_contains => False.elim ((contains_nothing i) empty_contains))
            (fun not_empty => False.elim (not_empty (createEmptyIsEmpty u))))
        (createEmptyIsEmpty u))

theorem insertContainsNew (v : Nat) (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) (h_inv : correctInvariants tree) :
  contains (treeInsert tree x) x := by
  induction v with
  | zero =>
    match tree with
    | vEBTree.Leaf _ =>
      rw [contains.eq_def]
      rw [treeInsert.eq_def]
      simp
  | succ u ih =>
    match tree with
    | vEBTree.Node h summary aux clusters =>
      rw [contains.eq_def]
      rw [treeInsert.eq_def]
      simp
      match summary with
      | some (mi, ma) =>
        simp
        by_cases h_mi_eq_x : mi = x
        · simp [h_mi_eq_x]
        · simp [h_mi_eq_x]
          by_cases h_x_lt_mi : x < mi
          · simp [h_x_lt_mi]
          · simp [h_x_lt_mi, h_mi_eq_x]
            rw [updateFin]
            simp
            rw [correctInvariants] at h_inv
            exact ih (clusters (high u x)) (low u x) (h_inv.left.right (high u x))
      | none =>
        simp

theorem insertContainsOld (v : Nat) (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) (h_inv : correctInvariants tree):
  ∀ i, ¬i = x → (contains tree i ↔ contains (treeInsert tree x) i) := by
  induction v with
  | zero =>
    match tree with
    | vEBTree.Leaf f =>
      exact (fun i => by
        rw [contains, treeInsert, contains]
        simp
        exact (fun i_not_x => fun i_x => False.elim (i_not_x i_x)))
  | succ u ih =>
    match tree with
    | vEBTree.Node h summary aux clusters =>
      exact (fun i i_not_x => by
        rw [contains.eq_def, treeInsert.eq_def, contains.eq_def]
        match summary with
        | some (mi, ma) =>
          simp
          rw [correctInvariants] at h_inv
          by_cases h_mi : mi = x
          · simp [h_mi]
          · simp [h_mi]
            by_cases x_lt_mi : x < mi
            · simp [x_lt_mi]
              rw [updateFin]
              by_cases high_i_mi : high u i = high u mi
              · simp [high_i_mi]
                rw [←ne_eq, ne_comm, ne_eq] at i_not_x
                simp [i_not_x]
                by_cases mi_eq_i : mi = i
                · simp [mi_eq_i]
                  exact insertContainsNew u (clusters (high u i)) (low u i) (h_inv.left.right (high u i))
                · simp [mi_eq_i]
                  have low_i_not_mi : low u i ≠ low u mi :=
                    byContradiction (fun low_i_mi => by
                      simp at low_i_mi
                      rw [←ne_eq, ne_comm, ne_eq] at mi_eq_i
                      exact mi_eq_i (eqDivMod u i mi high_i_mi low_i_mi)
                    )
                  exact ih (clusters (high u mi)) (low u mi) (h_inv.left.right (high u mi)) (low u i) low_i_not_mi
              · simp [high_i_mi]
                have mi_not_i : ¬mi = i :=
                  byContradiction (fun mi_eq_i => by
                    simp at mi_eq_i
                    simp [mi_eq_i] at high_i_mi
                  )
                rw [←ne_eq, ne_comm, ne_eq] at i_not_x
                simp [mi_not_i, i_not_x]
            · simp [x_lt_mi]
              by_cases mi_not_i : mi = i
              · simp [mi_not_i]
              · simp [mi_not_i]
                rw [updateFin]
                by_cases high_i_x : high u i = high u x
                · simp [high_i_x]
                  have low_i_neq_x : low u i ≠ low u x :=
                    byContradiction (fun low_i_x => by
                      simp at low_i_x
                      exact i_not_x (eqDivMod u i x high_i_x low_i_x)
                    )
                  exact ih (clusters (high u x)) (low u x) (h_inv.left.right (high u x)) (low u i) low_i_neq_x
                · simp [high_i_x]
        | none =>
          rw [correctInvariants] at h_inv
          simp at h_inv
          simp
          exact And.intro
            (fun h_eq => i_not_x (Eq.symm h_eq))
            (by
              have aux_contains_nothing := emptyContainsNothing u aux h_inv.left.left
              simp [h_inv.right.right] at aux_contains_nothing
              rw [containsNothing] at aux_contains_nothing
              have cluster_iff := h_inv.right.left (high u i)
              simp [aux_contains_nothing (high u i)] at cluster_iff
              have cluster_empty := emptyContainsNothing u (clusters (high u i)) (h_inv.left.right (high u i))
              simp [cluster_iff] at cluster_empty
              rw [containsNothing] at cluster_empty
              exact cluster_empty (low u i)))

theorem insertNonEmpty {v : Nat} (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) :
  ¬isEmpty (treeInsert tree x) :=
  match v, tree with
  | 0, vEBTree.Leaf f => by
    rw [treeInsert.eq_def]
    rw [isEmpty]
    simp
    exact Exists.intro x (by simp)
  | _ + 1, vEBTree.Node _ summary _ _ => by
    rw [treeInsert.eq_def]
    rw [isEmpty.eq_def]
    simp
    match summary with
    | some (mi, ma) =>
      simp
      by_cases x_eq_mi : mi = x
      · simp [x_eq_mi]
      · simp [x_eq_mi]
        by_cases x_lt_mi : x < mi
        · simp [x_lt_mi]
        · simp [x_lt_mi]
    | none =>
      simp

theorem treeInsertInvariants (v : Nat) (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) (h_inv : correctInvariants tree) :
  correctInvariants (treeInsert tree x) := by
  induction v with
  | zero =>
    match tree with
    | vEBTree.Leaf f =>
      rw [correctInvariants.eq_def]
      rw [treeInsert]
      simp
  | succ u ih =>
    match tree with
    | vEBTree.Node h summary aux clusters =>
      rw [correctInvariants.eq_def]
      rw [treeInsert.eq_def]
      simp
      match summary with
      | none =>
        simp
        rw [correctMin.eq_def]
        simp
        rw [correctInvariants] at h_inv
        simp at h_inv
        have aux_contains_nothing := (emptyContainsNothing u aux h_inv.left.left).mp h_inv.right.right
        rw [containsNothing] at aux_contains_nothing
        simp [aux_contains_nothing] at h_inv
        simp [aux_contains_nothing]
        have clusters_contains_nothing : ∀ i, ∀ j, ¬contains (clusters i) j :=
          fun i j => by
            have cluster_empty := (emptyContainsNothing u (clusters i) (h_inv.left.right i)).mp (h_inv.right.left i)
            rw [containsNothing] at cluster_empty
            simp [cluster_empty]
        exact And.intro
          h_inv.left
          (And.intro
            h_inv.right.left
            (And.intro
              (And.intro
                (fun i => by
                  by_cases x_eq_i : x = i
                  · simp [x_eq_i]
                  · rw [contains]
                    simp [x_eq_i]
                    simp [clusters_contains_nothing])
                (clusters_contains_nothing (high u x) (low u x)))
              (And.intro
                (fun i => by
                  by_cases x_eq_i : x = i
                  · simp [x_eq_i]
                  · rw [contains]
                    simp [x_eq_i]
                    simp [clusters_contains_nothing])
                (by
                  rw [contains]
                  simp))))
      | some (mi, ma) =>
        simp
        by_cases mi_eq_x : mi = x
        · rw [if_pos mi_eq_x]
          exact h_inv
        · simp [mi_eq_x]
          by_cases x_lt_mi : x < mi
          · simp [x_lt_mi]
            exact And.intro
              (And.intro
                (by
                  by_cases empty_cluster : isEmpty (clusters (high u mi))
                  · simp [empty_cluster]
                    exact ih aux (high u mi) h_inv.left.left
                  · simp [empty_cluster]
                    exact h_inv.left.left)
                (fun i => by
                  rw [updateFin]
                  by_cases i_eq_high : i = high u mi
                  · simp [i_eq_high]
                    exact ih (clusters (high u mi)) (low u mi) (h_inv.left.right (high u mi))
                  · simp [i_eq_high]
                    exact h_inv.left.right i))
              (And.intro
                (fun i => by
                  rw [updateFin]
                  by_cases i_eq_high : i = high u mi
                  · simp [i_eq_high]
                    simp [insertNonEmpty (clusters (high u mi)) (low u mi)]
                    by_cases empty_cluster : isEmpty (clusters (high u mi))
                    · simp [empty_cluster]
                      exact insertContainsNew u aux (high u mi) h_inv.left.left
                    · simp [empty_cluster]
                      simp [h_inv.right.left (high u mi)]
                      exact empty_cluster
                  · simp [i_eq_high]
                    by_cases empty_cluster : isEmpty (clusters (high u mi))
                    · simp [empty_cluster]
                      simp [←h_inv.right.left i]
                      simp [insertContainsOld u aux (high u mi) h_inv.left.left i i_eq_high]
                    · simp [empty_cluster]
                      simp [←h_inv.right.left i])
                (And.intro
                  (by
                    rw [correctMin]
                    exact And.intro
                      (fun i => by
                        by_cases x_eq_i : x = i
                        · simp [x_eq_i]
                        · simp [x_eq_i]
                          exact (fun contains_i => by
                            rw [contains] at contains_i
                            simp [x_eq_i] at contains_i
                            rw [updateFin] at contains_i
                            have ih_min := h_inv.right.right.left.left i
                            by_cases mi_eq_i : mi = i
                            · simp [←mi_eq_i]
                              exact x_lt_mi
                            · rw [contains] at ih_min
                              simp [mi_eq_i] at ih_min
                              by_cases high_eq : high u i = high u mi
                              · simp [high_eq] at contains_i
                                have low_neq : low u i ≠ low u mi := byContradiction (
                                    fun low_eq => by
                                      simp at low_eq
                                      simp [eqDivMod u i mi high_eq low_eq] at mi_eq_i
                                  )
                                have contains_cluster_old := insertContainsOld u (clusters (high u mi)) (low u mi) (h_inv.left.right (high u mi)) (low u i) low_neq
                                simp [←contains_cluster_old] at contains_i
                                rw [←high_eq] at contains_i
                                exact lt_trans x_lt_mi (ih_min contains_i)
                              · simp [high_eq] at contains_i
                                exact lt_trans (x_lt_mi) (ih_min contains_i)))
                      (by
                        have ih_min := h_inv.right.right.left.left x
                        rw [contains] at ih_min
                        simp [mi_eq_x] at ih_min
                        rw [updateFin]
                        have x_not_lt_mi : ¬mi < x := by
                          simp
                          exact le_iff_eq_or_lt.mpr (Or.inr (x_lt_mi))
                        rw [transformKeysLt] at x_lt_mi
                        by_cases high_eq : high u x = high u mi
                        · simp [high_eq]
                          simp [high_eq] at x_lt_mi
                          simp [←insertContainsOld u (clusters (high u mi)) (low u mi) (h_inv.left.right (high u mi)) (low u x) (lt_iff_le_and_ne.mp x_lt_mi).right]
                          simp [high_eq] at ih_min
                          simp [x_not_lt_mi] at ih_min
                          exact ih_min
                        · simp [high_eq]
                          simp [high_eq] at x_lt_mi
                          simp [x_not_lt_mi] at ih_min
                          exact ih_min))
                  (And.intro
                    (fun i => by
                      have ih_max := h_inv.right.right.right.left i
                      rw [contains] at ih_max
                      rw [contains]
                      by_cases x_eq_i : x = i
                      · simp [x_eq_i]
                      · simp [x_eq_i]
                        rw [updateFin]
                        by_cases high_eq : high u i = high u mi
                        · simp [high_eq]
                          by_cases mi_eq_i : mi = i
                          · simp [mi_eq_i] at ih_max
                            simp [ih_max]
                          · simp [mi_eq_i] at ih_max
                            have low_neq : low u i ≠ low u mi := byContradiction (
                              fun low_eq => by
                                simp at low_eq
                                simp [eqDivMod u i mi high_eq low_eq] at mi_eq_i
                            )
                            have contains_cluster_old := insertContainsOld u (clusters (high u mi)) (low u mi) (h_inv.left.right (high u mi)) (low u i) low_neq
                            simp [←contains_cluster_old]
                            rw [high_eq] at ih_max
                            exact (fun contains_i => Or.inl (ih_max contains_i))
                        · simp [high_eq]
                          by_cases mi_eq_i : mi = i
                          · simp [mi_eq_i] at ih_max
                            simp [ih_max]
                          · simp [mi_eq_i] at ih_max
                            exact (fun contains_i => Or.inl (ih_max contains_i)))
                    (by
                      rw [contains]
                      by_cases x_ma : x = ma ⊔ x
                      · rw [if_pos x_ma]
                        simp
                      · have max_eq_ma : ma ⊔ x = ma := by
                          simp [x_ma]
                          simp at x_ma
                          exact le_iff_eq_or_lt.mpr (Or.inr x_ma)
                        rw [if_neg x_ma]
                        rw [updateFin]
                        simp [max_eq_ma]
                        have ih_max := h_inv.right.right.right.right
                        rw [contains] at ih_max
                        by_cases high_eq : high u ma = high u mi
                        · simp [high_eq]
                          simp [←high_eq]
                          by_cases low_eq : low u ma = low u mi
                          · rw [←low_eq]
                            exact insertContainsNew u (clusters (high u ma)) (low u ma) (h_inv.left.right (high u ma))
                          · by_cases mi_eq_ma : mi = ma
                            · rw [mi_eq_ma]
                              exact insertContainsNew u (clusters (high u ma)) (low u ma) (h_inv.left.right (high u ma))
                            · simp [mi_eq_ma] at ih_max
                              simp [←insertContainsOld u (clusters (high u ma)) (low u mi) (h_inv.left.right (high u ma)) (low u ma) (by simp [low_eq])]
                              exact ih_max
                        · simp [high_eq]
                          by_cases mi_eq_ma : mi = ma
                          · rw [mi_eq_ma] at high_eq
                            contradiction
                          · simp [mi_eq_ma] at ih_max
                            exact ih_max))))
          · simp [x_lt_mi]
            exact And.intro
              (And.intro
                (by
                  by_cases empty_cluster : isEmpty (clusters (high u x))
                  · simp [empty_cluster]
                    exact ih aux (high u x) h_inv.left.left
                  · simp [empty_cluster]
                    exact h_inv.left.left)
                (fun i => by
                  rw [updateFin]
                  by_cases i_eq_high : i = high u x
                  · simp [i_eq_high]
                    exact ih (clusters (high u x)) (low u x) (h_inv.left.right (high u x))
                  · simp [i_eq_high]
                    exact h_inv.left.right i))
              (And.intro
                (fun i => by
                  rw [updateFin]
                  by_cases i_eq_high : i = high u x
                  · simp [i_eq_high]
                    simp [insertNonEmpty (clusters (high u x)) (low u x)]
                    by_cases empty_cluster : isEmpty (clusters (high u x))
                    · simp [empty_cluster]
                      exact insertContainsNew u aux (high u x) h_inv.left.left
                    · simp [empty_cluster]
                      simp [h_inv.right.left (high u x)]
                      exact empty_cluster
                  · simp [i_eq_high]
                    by_cases empty_cluster : isEmpty (clusters (high u x))
                    · simp [empty_cluster]
                      simp [←h_inv.right.left i]
                      simp [insertContainsOld u aux (high u x) h_inv.left.left i i_eq_high]
                    · simp [empty_cluster]
                      simp [←h_inv.right.left i])
                (And.intro
                  (by
                    rw [correctMin]
                    exact And.intro
                      (fun i => by
                        by_cases mi_eq_i : mi = i
                        · simp [mi_eq_i]
                        · simp [mi_eq_i]
                          exact (fun contains_i => by
                            rw [contains] at contains_i
                            simp [mi_eq_i] at contains_i
                            rw [updateFin] at contains_i
                            have ih_min := h_inv.right.right.left.left i
                            rw [contains] at ih_min
                            simp [mi_eq_i] at ih_min
                            simp at x_lt_mi
                            by_cases high_eq : high u i = high u x
                            · simp [high_eq] at contains_i
                              by_cases x_eq_i : i = x
                              · simp [x_eq_i]
                                simp [x_eq_i] at mi_eq_i
                                exact lt_iff_le_and_ne.mpr (And.intro x_lt_mi mi_eq_i)
                              · have low_neq : low u i ≠ low u x := byContradiction (
                                    fun low_eq => by
                                      simp at low_eq
                                      simp [eqDivMod u i x high_eq low_eq] at x_eq_i
                                  )
                                have contains_cluster_old := insertContainsOld u (clusters (high u x)) (low u x) (h_inv.left.right (high u x)) (low u i) low_neq
                                simp [←contains_cluster_old] at contains_i
                                rw [←high_eq] at contains_i
                                exact ih_min contains_i
                            · simp [high_eq] at contains_i
                              exact ih_min contains_i))
                      (by
                        have ih_min := h_inv.right.right.left.left mi
                        rw [contains] at ih_min
                        simp [mi_eq_x] at ih_min
                        rw [updateFin]
                        simp at x_lt_mi
                        rw [transformKeysLe] at x_lt_mi
                        by_cases high_eq : high u mi = high u x
                        · have low_neq : low u mi ≠ low u x := byContradiction (
                              fun low_eq => by
                                simp at low_eq
                                simp [eqDivMod u mi x high_eq low_eq] at mi_eq_x
                            )
                          simp [high_eq]
                          simp [high_eq] at x_lt_mi
                          simp [←insertContainsOld u (clusters (high u x)) (low u x) (h_inv.left.right (high u x)) (low u mi) low_neq]
                          simp [←high_eq]
                          exact h_inv.right.right.left.right
                        · simp [high_eq]
                          exact h_inv.right.right.left.right))
                  (And.intro
                    (fun i => by
                      have ih_max := h_inv.right.right.right.left i
                      rw [contains] at ih_max
                      rw [contains]
                      by_cases mi_eq_i : mi = i
                      · simp [mi_eq_i]
                        simp [mi_eq_i] at ih_max
                        exact Or.inl ih_max
                      · simp [mi_eq_i]
                        rw [updateFin]
                        by_cases high_eq : high u i = high u x
                        · simp [high_eq]
                          by_cases x_eq_i : x = i
                          · simp [mi_eq_i] at ih_max
                            rw [x_eq_i]
                            simp [ih_max]
                          · simp [mi_eq_i] at ih_max
                            have low_neq : low u i ≠ low u x := byContradiction (
                              fun low_eq => by
                                simp at low_eq
                                simp [eqDivMod u i x high_eq low_eq] at x_eq_i
                            )
                            have contains_cluster_old := insertContainsOld u (clusters (high u x)) (low u x) (h_inv.left.right (high u x)) (low u i) low_neq
                            simp [←contains_cluster_old]
                            rw [high_eq] at ih_max
                            exact (fun contains_i => Or.inl (ih_max contains_i))
                        · simp [high_eq]
                          by_cases mi_eq_i : mi = i
                          · simp [mi_eq_i] at ih_max
                            simp [ih_max]
                          · simp [mi_eq_i] at ih_max
                            exact (fun contains_i => Or.inl (ih_max contains_i)))
                    (by
                      rw [contains]
                      have mi_neq_ma : mi ≠ ma ⊔ x := by
                        simp at x_lt_mi
                        simp
                        exact byContradiction (
                          fun mi_eq => by
                            simp at mi_eq
                            have x_le_mi : x ≤ mi := by
                              rw [mi_eq]
                              apply le_sup_right
                            exact mi_eq_x (le_antisymm x_lt_mi x_le_mi)
                        )
                      simp [mi_neq_ma]
                      by_cases x_ma : x = ma ⊔ x
                      · rw [updateFin]
                        rw [←x_ma]
                        simp
                        exact insertContainsNew u (clusters (high u x)) (low u x) (h_inv.left.right (high u x))
                      · have max_eq_ma : ma ⊔ x = ma := by
                          simp [x_ma]
                          simp at x_ma
                          exact le_iff_eq_or_lt.mpr (Or.inr x_ma)
                        rw [updateFin]
                        simp [max_eq_ma]
                        have ih_max := h_inv.right.right.right.right
                        rw [contains] at ih_max
                        have mi_neq_ma : mi ≠ ma := byContradiction (
                            fun mi_eq_ma => by
                              have x_le_ma : x ≤ ma := by
                                rw [←max_eq_ma]
                                apply le_sup_right
                              simp at mi_eq_ma
                              rw [←mi_eq_ma] at x_le_ma
                              simp at x_lt_mi
                              exact mi_eq_x (le_antisymm x_lt_mi x_le_ma)
                          )
                        by_cases high_eq : high u ma = high u x
                        · simp [high_eq]
                          simp [←high_eq]
                          by_cases low_eq : low u ma = low u x
                          · rw [←low_eq]
                            exact insertContainsNew u (clusters (high u ma)) (low u ma) (h_inv.left.right (high u ma))
                          · by_cases x_eq_ma : x = ma
                            · rw [x_eq_ma]
                              exact insertContainsNew u (clusters (high u ma)) (low u ma) (h_inv.left.right (high u ma))
                            · simp [x_eq_ma] at ih_max
                              simp [←insertContainsOld u (clusters (high u ma)) (low u x) (h_inv.left.right (high u ma)) (low u ma) (by simp [low_eq])]
                              exact ih_max mi_neq_ma
                        · simp [high_eq]
                          by_cases x_eq_ma : x = ma
                          · rw [x_eq_ma] at high_eq
                            contradiction
                          · simp [x_eq_ma] at ih_max
                            exact ih_max mi_neq_ma))))
