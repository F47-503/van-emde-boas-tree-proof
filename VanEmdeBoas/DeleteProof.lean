import Mathlib.Tactic
import VanEmdeBoas.Defs
import VanEmdeBoas.UtilLemmas
import VanEmdeBoas.Operations
import VanEmdeBoas.Invariants

open Classical

theorem recalcSummaryCorrect {v : Nat} (tree : vEBTree v) (h_rec : recursiveCorrectInvariants tree) :
  correctInvariants (recalcSummary (tree)) := by
  match v, tree with
  | 0, vEBTree.Leaf f =>
    rw [recalcSummary]
    rw [correctInvariants]
    simp
  | u + 1, vEBTree.Node _ summary aux clusters =>
    rw [recalcSummary.eq_def]
    rw [correctInvariants.eq_def]
    rw [recursiveCorrectInvariants.eq_def] at h_rec
    simp at h_rec
    match summary with
    | some (mi, ma) =>
      simp
      rw [correctMin] at h_rec
      simp at h_rec
      simp [h_rec]
      rw [constructiveMax]
      by_cases empty_aux : isEmpty aux
      · simp [empty_aux]
        rw [correctMin]
        exact And.intro
          (have h_min := h_rec.right.right
          And.intro
            (fun i => by
              have h_min_i := h_min.left i
              rw [contains] at h_min_i
              rw [contains]
              exact h_min_i)
            (h_min.right))
          (And.intro
            (fun i => by
              rw [contains]
              by_cases mi_eq_i : mi = i
              · simp [mi_eq_i]
              · simp [mi_eq_i]
                have aux_not_contains := (emptyContainsNothing u aux h_rec.left.left).mp empty_aux
                rw [containsNothing] at aux_not_contains
                have empty_i := aux_not_contains (high u i)
                simp [h_rec.right.left (high u i)] at empty_i
                have not_contains_i := (emptyContainsNothing u (clusters (high u i)) (h_rec.left.right (high u i))).mp empty_i
                rw [containsNothing] at not_contains_i
                simp [not_contains_i])
            (by
              rw [contains]
              simp))
      · simp [empty_aux]
        have h_max := getMaxReturnsMax u aux h_rec.left.left empty_aux
        by_cases cluster_empty : isEmpty (clusters (getMax! u aux empty_aux))
        · simp [cluster_empty]
          have aux_prop := h_rec.right.left (getMax! u aux empty_aux)
          simp [h_max.right] at aux_prop
          exact False.elim (aux_prop cluster_empty)
        · simp [cluster_empty]
          exact And.intro
            (by
              rw [correctMin]
              simp
              simp [h_rec]
              exact (fun i => by
                rw [contains]
                have h_rec_min := h_rec.right.right.left i
                rw [contains] at h_rec_min
                exact h_rec_min))
            (have h_max_cluster := getMaxReturnsMax u (clusters (getMax! u aux empty_aux)) (h_rec.left.right (getMax! u aux empty_aux)) cluster_empty
            And.intro
              (fun i hi => by
                rw [contains] at hi
                simp at hi
                rw [transformKeysLe]
                simp [composeCorrectHigh, composeCorrectLow]
                by_cases mi_eq_i : mi = i
                · have h_min := h_rec.right.right.left (compose u (getMax! u aux empty_aux) (getMax! u (clusters (getMax! u aux empty_aux)) cluster_empty))
                  rw [contains] at h_min
                  rw [composeCorrectHigh, composeCorrectLow] at h_min
                  by_cases mi_eq : mi = compose u (getMax! u aux empty_aux) (getMax! u (clusters (getMax! u aux empty_aux)) cluster_empty)
                  · rw [←mi_eq_i]
                    rw [mi_eq]
                    rw [composeCorrectHigh, composeCorrectLow]
                    simp
                  · simp [mi_eq] at h_min
                    simp [h_max_cluster.right] at h_min
                    rw [transformKeysLt] at h_min
                    rw [composeCorrectHigh, composeCorrectLow] at h_min
                    rw [←mi_eq_i]
                    exact Or.elim h_min
                      (fun high_neq => Or.inl high_neq)
                      (fun high_eq => Or.inr (by
                        simp [lt_iff_le_and_ne] at high_eq
                        simp [high_eq]))
                · simp [mi_eq_i] at hi
                  have h_max_i := h_max.left (high u i)
                  have aux_contains : contains aux (high u i) := byContradiction (
                    fun not_contains => by
                      have aux_i := h_rec.right.left (high u i)
                      simp [not_contains] at aux_i
                      have contains_nothing_i := emptyContainsNothing u (clusters (high u i)) (h_rec.left.right (high u i))
                      simp [aux_i] at contains_nothing_i
                      rw [containsNothing] at contains_nothing_i
                      exact (contains_nothing_i (low u i)) hi
                  )
                  simp [aux_contains] at h_max_i
                  rw [le_iff_eq_or_lt] at h_max_i
                  exact Or.elim h_max_i
                    (fun high_eq => by
                      simp [high_eq]
                      have h_max_cluster_i := h_max_cluster.left (low u i)
                      rw [high_eq] at hi
                      simp [hi] at h_max_cluster_i
                      exact h_max_cluster_i)
                    (fun high_lt => Or.inl high_lt))
              (by
                rw [contains]
                simp [composeCorrectHigh, composeCorrectLow]
                exact (fun mi_neq => by
                  simp [h_max_cluster])))
    | none =>
      simp
      simp [h_rec]

theorem recalcKeepsContains {v : Nat} (tree : vEBTree v) :
  ∀ x, contains (recalcSummary tree) x ↔ contains tree x := fun x => by
  match v, tree with
  | 0, vEBTree.Leaf f =>
    rw [recalcSummary]
  | u + 1, vEBTree.Node h summary aux clusters =>
    rw [recalcSummary.eq_def]
    rw [contains.eq_def]
    simp
    match summary with
    | some (mi, ma) =>
      simp
      match constructiveMax (vEBTree.Node h summary aux clusters) with
      | some res =>
        simp
        nth_rw 2 [contains.eq_def]
        simp
      | none =>
        simp
        nth_rw 2 [contains.eq_def]
        simp
    | none =>
      simp
      rw [contains]
      simp

theorem getMinContains {v : Nat} (tree : vEBTree v) (h_non_empty : ¬isEmpty tree) : contains tree (getMin! v tree h_non_empty) := by
  match v, tree with
  | 0, vEBTree.Leaf f =>
    rw [isEmpty] at h_non_empty
    simp at h_non_empty
    rw [contains]
    rw [getMin!]
    exact Exists.elim h_non_empty (
      fun x hx => Or.elim (zeroOrOneLe x)
        (fun x0 => by
          rw [x0] at hx
          simp [hx])
        (fun x1 => by
          by_cases f0 : f 0
          · simp [f0]
          · simp [f0]
            rw [x1] at hx
            exact hx)
    )
  | u + 1, vEBTree.Node h summary aux clusters =>
    match summary with
    | some (mi, ma) =>
      rw [contains.eq_def]
      rw [getMin!.eq_def]
      simp
    | none => contradiction

theorem containsConstructiveMin {v : Nat} (tree : vEBTree v) (h_non_empty : ¬isEmpty tree) (h_rec : recursiveCorrectInvariants tree):
  constructiveMin tree = none ∧ (∀ i, getMin! v tree h_non_empty ≠ i → ¬contains tree i) ∨ ∃ res, constructiveMin tree = some res ∧ contains tree res ∧ (v > 0 → getMin! v tree h_non_empty ≠ res) := by
  induction v with
  | zero =>
    match tree with
    | vEBTree.Leaf f =>
      rw [constructiveMin]
      simp
      rw [isEmpty] at h_non_empty
      simp at h_non_empty
      exact Exists.elim h_non_empty (
        fun y hy =>
          Or.elim (zeroOrOneLe y)
            (fun y0 => by
              rw [y0] at hy
              simp [hy]
              rw [contains]
              exact hy)
            (fun y1 => by
              rw [y1] at hy
              by_cases f0 : f 0
              · simp [f0]
                rw [contains]
                exact f0
              · simp [f0]
                rw [contains]
                exact hy)
      )
  | succ u ih =>
    match tree with
    | vEBTree.Node h summary aux clusters =>
      rw [constructiveMin]
      rw [recursiveCorrectInvariants.eq_def] at h_rec
      simp at h_rec
      by_cases aux_empty : isEmpty aux
      · simp [aux_empty]
        have aux_contains_nothing := (emptyContainsNothing u aux h_rec.left.left).mp aux_empty
        rw [containsNothing] at aux_contains_nothing
        exact (
          fun i i_not_min => by
            rw [contains.eq_def]
            simp
            rw [isEmpty] at h_non_empty
            simp at h_non_empty
            match summary with
            | some (mi, ma) =>
              simp
              rw [getMin!] at i_not_min
              simp [i_not_min]
              have cluster_empty := aux_contains_nothing (high u i)
              rw [h_rec.right.left (high u i)] at cluster_empty
              simp at cluster_empty
              have cluster_not_contains := (emptyContainsNothing u (clusters (high u i)) (h_rec.left.right (high u i))).mp cluster_empty
              rw [containsNothing] at cluster_not_contains
              exact cluster_not_contains (low u i)
            | none => contradiction)
      · simp [aux_empty]
        by_cases cluster_empty : isEmpty (clusters (getMin! u aux aux_empty))
        · simp [cluster_empty]
          match summary with
          | some (mi, ma) =>
            exact (
              fun i i_not_min => by
                rw [getMin!] at i_not_min
                rw [contains]
                simp [i_not_min]
                rw [correctMin] at h_rec
                simp at h_rec
                have aux_contains := getMinContains aux aux_empty
                have aux_min_correct := h_rec.right.left (getMin! u aux aux_empty)
                simp at aux_contains
                simp [aux_contains] at aux_min_correct
                exact False.elim (aux_min_correct cluster_empty))
          | none => contradiction
        · simp [cluster_empty]
          rw [contains.eq_def]
          simp
          match summary with
          | some (mi, ma) =>
            simp
            exact And.intro
              (fun min_neq => by
                rw [composeCorrectHigh, composeCorrectLow]
                simp [getMinContains])
              (by
                rw [getMin!]
                rw [correctMin] at h_rec
                exact byContradiction (
                  fun mi_eq => by
                    simp at mi_eq
                    rw [mi_eq] at h_rec
                    rw [composeCorrectHigh, composeCorrectLow] at h_rec
                    simp [getMinContains] at h_rec
                ))
          | none => contradiction

theorem deleteContains (v : Nat) (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) (h_rec : correctInvariants tree) :
  ∀ y, if y = x then ¬contains (treeDelete tree x) y else contains (treeDelete tree x) y ↔ contains tree y := by
  induction v with
  | zero =>
    match tree with
    | vEBTree.Leaf f =>
      exact (fun y => by
        rw [contains.eq_def]
        rw [treeDelete]
        simp
        by_cases y_eq_x : y = x
        · simp [y_eq_x]
        · simp [y_eq_x]
          rw [contains]
      )
  | succ u ih =>
    match tree with
    | vEBTree.Node h summary aux clusters =>
      exact (fun y => by
        rw [treeDelete.eq_def]
        simp
        match summary with
        | some (mi, ma) =>
          simp
          by_cases y_eq_x : y = x
          · simp [y_eq_x]
            by_cases mi_eq_x : mi = x
            · simp [mi_eq_x]
              by_cases ma_eq_x : ma = x
              · simp [ma_eq_x]
                rw [contains]
                simp
              · simp [ma_eq_x]
                have h_non_empty : ¬isEmpty (vEBTree.Node h (some (x, ma)) aux clusters) := by
                  simp [isEmpty]
                rw [correctInvariants] at h_rec
                have rec_correct : recursiveCorrectInvariants (vEBTree.Node h (some (x, ma)) aux clusters) := by
                  rw [recursiveCorrectInvariants]
                  simp [←mi_eq_x]
                  simp [h_rec]
                exact Or.elim (containsConstructiveMin (vEBTree.Node h (some (x, ma)) aux clusters) h_non_empty rec_correct)
                  (fun min_none => by
                    simp [min_none]
                    rw [contains]
                    simp)
                  (fun min_res =>
                    Exists.elim min_res (
                      fun res h_res => by
                        simp [h_res]
                        simp [recalcKeepsContains]
                        rw [contains]
                        by_cases res_eq_x : res = x
                        · simp [res_eq_x]
                          have res_contains := h_res.right.right
                          simp at res_contains
                          rw [getMin!] at res_contains
                          simp [res_eq_x] at res_contains
                        · simp [res_eq_x]
                          rw [updateFin]
                          by_cases high_eq : high u x = high u res
                          · simp [high_eq]
                            have low_neq : low u x ≠ low u res := byContradiction (
                              fun low_eq => by
                                simp at low_eq
                                have eq := eqDivMod u x res high_eq low_eq
                                simp [eq] at res_eq_x
                            )
                            have h_cluster := ih (clusters (high u res)) (low u res) (h_rec.left.right (high u res)) (low u x)
                            simp [low_neq] at h_cluster
                            simp [h_cluster]
                            simp [←high_eq]
                            rw [recursiveCorrectInvariants] at rec_correct
                            rw [correctMin] at rec_correct
                            simp [rec_correct]
                          · simp [high_eq]
                            rw [recursiveCorrectInvariants] at rec_correct
                            rw [correctMin] at rec_correct
                            simp [rec_correct]
                    ))
            · simp [mi_eq_x]
              simp [recalcKeepsContains]
              rw [contains.eq_def]
              simp
              exact And.intro
                mi_eq_x
                (by
                  rw [updateFin]
                  simp
                  have h_cluster := ih (clusters (high u x)) (low u x) (h_rec.left.right (high u x)) (low u x)
                  simp at h_cluster
                  exact h_cluster)
          · simp [y_eq_x]
            have x_neq_y : ¬x = y :=
              (byContradiction (
                fun x_eq_y => by
                  simp at x_eq_y
                  simp [x_eq_y] at y_eq_x
              ))
            by_cases mi_eq_x : mi = x
            · simp [mi_eq_x]
              by_cases ma_eq_x : ma = x
              · simp [ma_eq_x]
                rw [contains, contains]
                simp
                exact And.intro
                  x_neq_y
                  (byContradiction (
                    fun y_contains => by
                      simp at y_contains
                      rw [correctInvariants] at h_rec
                      have h_max := h_rec.right.right.right.left y
                      rw [contains] at h_max
                      simp [y_contains] at h_max
                      rw [correctMin] at h_rec
                      have h_min := h_rec.right.right.left.left y
                      have mi_neq_y : mi ≠ y := byContradiction (
                        fun mi_eq_y => by
                          simp at mi_eq_y
                          simp [mi_eq_x] at mi_eq_y
                          simp [mi_eq_y] at y_eq_x
                      )
                      simp [mi_neq_y] at h_min
                      rw [contains] at h_min
                      simp [y_contains] at h_min
                      rw [mi_eq_x] at h_min
                      rw [←ma_eq_x] at h_min
                      have y_lt_y := lt_of_le_of_lt h_max h_min
                      simp at y_lt_y
                  ))
              · simp [ma_eq_x]
                have h_non_empty : ¬isEmpty (vEBTree.Node h (some (x, ma)) aux clusters) := by
                  simp [isEmpty]
                rw [correctInvariants] at h_rec
                have rec_correct : recursiveCorrectInvariants (vEBTree.Node h (some (x, ma)) aux clusters) := by
                  rw [recursiveCorrectInvariants]
                  simp [←mi_eq_x]
                  simp [h_rec]
                exact Or.elim (containsConstructiveMin (vEBTree.Node h (some (x, ma)) aux clusters) h_non_empty rec_correct)
                  (fun min_none => by
                    simp [min_none]
                    rw [contains]
                    simp
                    rw [contains]
                    simp
                    have min_none_correct := min_none.right y
                    rw [getMin!] at min_none_correct
                    simp [x_neq_y]
                    rw [contains] at min_none_correct
                    simp at min_none_correct
                    simp [x_neq_y] at min_none_correct
                    exact min_none_correct)
                  (fun min_res =>
                    Exists.elim min_res (
                      fun res h_res => by
                        simp [h_res]
                        simp [recalcKeepsContains]
                        rw [contains]
                        by_cases res_eq_y : res = y
                        · simp [res_eq_y]
                          have res_contains := h_res.right
                          simp at res_contains
                          rw [getMin!] at res_contains
                          simp [res_eq_y] at res_contains
                          rw [contains]
                          simp [res_contains]
                          rw [contains] at res_contains
                          simp [res_contains.right] at res_contains
                          exact res_contains
                        · simp [res_eq_y]
                          rw [updateFin]
                          by_cases high_eq : high u y = high u res
                          · simp [high_eq]
                            have low_neq : low u y ≠ low u res := byContradiction (
                              fun low_eq => by
                                simp at low_eq
                                have eq := eqDivMod u y res high_eq low_eq
                                simp [eq] at res_eq_y
                            )
                            have h_cluster := ih (clusters (high u res)) (low u res) (h_rec.left.right (high u res)) (low u y)
                            simp [low_neq] at h_cluster
                            simp [h_cluster]
                            simp [←high_eq]
                            rw [recursiveCorrectInvariants] at rec_correct
                            rw [correctMin] at rec_correct
                            rw [contains]
                            simp [x_neq_y]
                          · simp [high_eq]
                            rw [recursiveCorrectInvariants] at rec_correct
                            rw [correctMin] at rec_correct
                            rw [contains]
                            simp [x_neq_y]
                    ))
            · simp [mi_eq_x]
              simp [recalcKeepsContains]
              rw [contains, contains]
              simp
              by_cases mi_eq_y : mi = y
              · simp [mi_eq_y]
              · simp [mi_eq_y]
                rw [updateFin]
                by_cases high_eq : high u y = high u x
                · simp [high_eq]
                  have low_neq : low u y ≠ low u x := byContradiction (
                    fun low_eq => by
                      simp at low_eq
                      have eq := eqDivMod u y x high_eq low_eq
                      simp [eq] at y_eq_x
                  )
                  have ih_cluster := ih (clusters (high u x)) (low u x) (h_rec.left.right (high u x)) (low u y)
                  simp [low_neq] at ih_cluster
                  exact ih_cluster
                · simp [high_eq]
        | none =>
          by_cases y_eq_x : y = x
          · simp [y_eq_x]
            rw [contains]
            simp
          · simp [y_eq_x]
      )

theorem deleteCorrectInvariants (v : Nat) (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) (h_inv : correctInvariants tree) :
  correctInvariants (treeDelete tree x) := by
  induction v with
  | zero => sorry
  | succ u ih => sorry
