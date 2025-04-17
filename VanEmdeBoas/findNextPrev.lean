import VanEmdeBoas.Invariants

open Classical

theorem findNextIsCorrect (v : Nat) (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) (h_aux : correctAux tree) (h_summary : correctSummary tree) :
  correctFindNext tree x := by
  induction v with
  | zero =>
    rw [correctFindNext]
    rw [findNext.eq_def]
    match tree with
    | vEBTree.Leaf f =>
      by_cases has_next : x = 0 ∧ f 1
      · simp [has_next]
        exact And.intro
          has_next.right
          (fun i h_i =>
            Or.elim (zeroOrOneLe i)
              (Or.inl)
              (fun i1 => Or.inr (by simp [i1])))
      · simp [has_next]
        simp at has_next
        exact (fun i =>
          Or.elim (zeroOrOneLe i)
            (fun hi₀ => Or.elim (zeroOrOneLe x)
              (fun hx₀ h => by
                rw [hi₀, hx₀])
              (fun hx₁ h => by
                rw [hi₀, hx₁]
                trivial))
            (fun hi₁ => Or.elim (zeroOrOneLe x)
              (fun hx₀ h => by
                rw [hi₁] at h
                rw [contains] at h
                rw [hx₀, h] at has_next
                trivial)
              (fun hx₁ h => by
                rw [hi₁, hx₁])))
  | succ u ih =>
    rw [correctFindNext]
    rw [findNext.eq_def]
    match tree with
    | vEBTree.Node h summary aux clusters =>
      rw [correctSummary.eq_def] at h_summary
      simp at h_summary
      rw [correctAux.eq_def] at h_aux
      simp at h_aux
      have recursive_summary : recursiveCorrectSummary (vEBTree.Node h summary aux clusters) := by
        rw [recursiveCorrectSummary]
        exact h_summary.left
      have h_aux_next := ih aux (high u x) h_aux.left h_summary.left.left
      rw [correctFindNext] at h_aux_next
      by_cases h_empty_cluster : isEmpty (clusters (high u x))
      · simp
        simp [h_empty_cluster]
        exact Or.elim h_aux_next
          (fun res_exists =>
            Exists.elim res_exists
              (fun res res_correct => by
                rw [←res_correct.left]
                simp
                by_cases h_empty_next : isEmpty (clusters res)
                · have h_not_contains_cluster := (h_aux.right.right res).mp h_empty_next
                  exact False.elim (h_not_contains_cluster res_correct.right.right.left)
                · simp [h_empty_next]
                  have h_min := getMinReturnsMin u (clusters res) (h_summary.left.right res) (h_aux.right.left res) h_empty_next
                  exact And.intro
                    (by
                      rw [transformKeysLt]
                      rw [composeCorrectHigh, composeCorrectLow]
                      exact Or.inl res_correct.right.left)
                    (And.intro
                      (by
                        rw [contains]
                        rw [composeCorrectHigh, composeCorrectLow]
                        simp
                        exact h_min.left)
                      (fun i h_i => or_iff_not_imp_left.mpr (
                          fun i_lt => by
                            simp at i_lt
                            rw [transformKeysLt] at i_lt
                            rw [transformKeysLe]
                            rw [composeCorrectHigh, composeCorrectLow]
                            rw [contains] at h_i
                            have aux_contains_i := containsAux (vEBTree.Node h summary aux clusters) i h_aux recursive_summary h_i
                            simp at aux_contains_i
                            have aux_le := res_correct.right.right.right (high u i) aux_contains_i
                            have x_not_i : high u x ≠ high u i := byContradiction (
                              fun x_eq_i => by
                                rw [not_not] at x_eq_i
                                rw [x_eq_i] at h_empty_cluster
                                rw [h_aux.right.right (high u i)] at h_empty_cluster
                                exact False.elim (h_empty_cluster aux_contains_i)
                            )
                            simp [x_not_i] at i_lt
                            exact Or.elim aux_le
                              (fun x_le_i => False.elim ((lt_iff_not_le.mp i_lt) x_le_i))
                              (fun res_le_i => Or.elim (le_iff_eq_or_lt.mp res_le_i)
                                (fun res_eq_i => by
                                  simp [res_eq_i]
                                  rw [←res_eq_i] at h_i
                                  have h_min_i := h_min.right (low u i) h_i
                                  simp [res_eq_i] at h_min_i
                                  exact h_min_i)
                                (fun res_lt_i => Or.inl res_lt_i)))))))
          (fun next_none => Or.inr (by
              simp [next_none]
              exact (fun i h_i => by
                rw [contains] at h_i
                rw [transformKeysLe]
                have aux_contains_i := containsAux (vEBTree.Node h summary aux clusters) i h_aux recursive_summary h_i
                simp at aux_contains_i
                have x_not_i : high u i ≠ high u x := byContradiction (
                  fun x_eq_i => by
                    rw [not_not] at x_eq_i
                    rw [←x_eq_i] at h_empty_cluster
                    rw [h_aux.right.right (high u i)] at h_empty_cluster
                    exact False.elim (h_empty_cluster aux_contains_i)
                )
                simp [x_not_i]
                have h_min_aux := next_none.right (high u i) aux_contains_i
                exact lt_iff_le_and_ne.mpr (And.intro h_min_aux x_not_i))))
      · simp
        simp [h_empty_cluster]
        have h_max := getMaxReturnsMax u (clusters (high u x)) (h_summary.left.right (high u x)) (h_aux.right.left (high u x)) h_empty_cluster
        have h_max_contains := h_max.left
        by_cases h_max_lt : low u x < getMax! u (clusters (high u x)) h_empty_cluster
        · simp [h_max_lt]
          have h_cluster_same := ih (clusters (high u x)) (low u x) (h_aux.right.left (high u x)) (h_summary.left.right (high u x))
          rw [correctFindNext] at h_cluster_same
          exact Or.elim (h_cluster_same)
            (fun next_exists => Exists.elim next_exists (
              fun res res_correct => Or.inl (by
                simp [←res_correct.left]
                exact And.intro
                  (by
                    rw [transformKeysLt]
                    rw [composeCorrectHigh, composeCorrectLow]
                    exact Or.inr (And.intro rfl (res_correct.right.left)))
                  (And.intro
                    (by
                      rw [contains]
                      rw [composeCorrectHigh, composeCorrectLow]
                      exact res_correct.right.right.left)
                    (fun i h_i => or_iff_not_imp_left.mpr (
                      fun x_lt_i => by
                        simp at x_lt_i
                        rw [transformKeysLe]
                        rw [composeCorrectHigh, composeCorrectLow]
                        rw [transformKeysLt] at x_lt_i
                        by_cases high_x_lt_i : high u x < high u i
                        · exact Or.inl high_x_lt_i
                        · simp [high_x_lt_i] at x_lt_i
                          simp [x_lt_i.left]
                          simp [x_lt_i.left] at res_correct
                          rw [contains] at h_i
                          exact Or.elim (res_correct.right.right.right (low u i) h_i)
                            (fun low_i_le_x => False.elim ((lt_iff_not_le.mp x_lt_i.right) low_i_le_x))
                            (fun res_le_i => res_le_i)))))))
            (fun next_empty =>
              have next_le := next_empty.right (getMax! u (clusters (high u x)) h_empty_cluster) h_max_contains
              False.elim (lt_iff_not_le.mp h_max_lt next_le))
        · simp [h_max_lt]
          simp at h_max_lt
          exact Or.elim h_aux_next
            (fun aux_next_exists => Exists.elim aux_next_exists (
              fun res res_correct => by
                simp [←res_correct.left]
                by_cases h_cluster_empty : isEmpty (clusters res)
                · have aux_not_contains_res := (h_aux.right.right res).mp h_cluster_empty
                  exact False.elim (aux_not_contains_res res_correct.right.right.left)
                · simp [h_cluster_empty]
                  have h_min := getMinReturnsMin u (clusters res) (h_summary.left.right res) (h_aux.right.left res) h_cluster_empty
                  exact And.intro
                    (by
                      rw [transformKeysLt]
                      rw [composeCorrectHigh, composeCorrectLow]
                      exact Or.inl (res_correct.right.left))
                    (And.intro
                      (by
                        rw [contains]
                        rw [composeCorrectHigh, composeCorrectLow]
                        exact h_min.left)
                      (fun i h_i => or_iff_not_imp_left.mpr (
                        fun x_lt_i => by
                          simp at x_lt_i
                          rw [transformKeysLe]
                          rw [transformKeysLt] at x_lt_i
                          rw [composeCorrectHigh, composeCorrectLow]
                          have aux_contains_i := containsAux (vEBTree.Node h summary aux clusters) i h_aux recursive_summary h_i
                          simp at aux_contains_i
                          have aux_le := res_correct.right.right.right (high u i) aux_contains_i
                          rw [contains] at h_i
                          exact Or.elim aux_le
                            (fun high_i_le_x => Or.elim x_lt_i
                              (fun high_x_lt_i => False.elim ((lt_iff_not_le.mp high_x_lt_i) high_i_le_x))
                              (fun high_x_eq_i => by
                                simp [high_x_eq_i.left] at h_max
                                simp [high_x_eq_i.left] at h_max_lt
                                have h_max_i := h_max.right (low u i) h_i
                                have low_i_le_x := le_trans h_max_i h_max_lt
                                exact False.elim ((lt_iff_not_le.mp high_x_eq_i.right) low_i_le_x)))
                            (fun res_le_i => Or.elim (le_iff_eq_or_lt.mp res_le_i)
                              (fun res_eq_i => Or.inr (
                                And.intro
                                  res_eq_i
                                  (by
                                    nth_rw 1 [←res_eq_i] at h_i
                                    exact h_min.right (low u i) h_i)))
                              (fun res_lt_i => Or.inl res_lt_i)))))))
            (fun aux_next_none => by
              simp [aux_next_none.left]
              exact (fun i h_i => by
                rw [transformKeysLe]
                rw [contains] at h_i
                have aux_contains_i := containsAux (vEBTree.Node h summary aux clusters) i h_aux recursive_summary h_i
                simp at aux_contains_i
                have aux_le := aux_next_none.right (high u i) aux_contains_i
                exact Or.elim (le_iff_eq_or_lt.mp aux_le)
                  (fun i_eq_x => by
                    simp [i_eq_x] at h_i
                    have h_max_le := h_max.right (low u i) h_i
                    simp [i_eq_x]
                    exact le_trans h_max_le h_max_lt)
                  (fun i_lt_x => Or.inl i_lt_x)))


theorem findPrevIsCorrect (v : Nat) (tree : vEBTree v) (x : Fin (2 ^ 2 ^ v)) (h_aux : correctAux tree) (h_summary : correctSummary tree) :
  correctFindPrev tree x := by
  induction v with
  | zero =>
    rw [correctFindPrev]
    rw [findPrev.eq_def]
    match tree with
    | vEBTree.Leaf f =>
      by_cases has_next : x = 1 ∧ f 0
      · simp [has_next]
        exact And.intro
          has_next.right
          (fun i h_i =>
            Or.elim (zeroOrOneLe i)
              (fun i0 => Or.inr (by simp [i0]))
              (fun i1 => Or.inl (by simp [i1])))
      · simp [has_next]
        simp at has_next
        exact (fun i =>
          Or.elim (zeroOrOneLe i)
            (fun hi₀ => Or.elim (zeroOrOneLe x)
              (fun hx₀ h => by
                rw [hi₀, hx₀])
              (fun hx₁ h => by
                rw [hi₀, contains] at h
                rw [hx₁, h] at has_next
                trivial))
            (fun hi₁ => Or.elim (zeroOrOneLe x)
              (fun hx₀ h => by
                rw [hi₁, hx₀]
                trivial)
              (fun hx₁ h => by
                rw [hi₁, hx₁])))
  | succ u ih =>
    rw [correctFindPrev]
    rw [findPrev.eq_def]
    match tree with
    | vEBTree.Node h summary aux clusters =>
      rw [correctSummary.eq_def] at h_summary
      simp at h_summary
      rw [correctAux.eq_def] at h_aux
      simp at h_aux
      have recursive_summary : recursiveCorrectSummary (vEBTree.Node h summary aux clusters) := by
        rw [recursiveCorrectSummary]
        exact h_summary.left
      have h_aux_prev := ih aux (high u x) h_aux.left h_summary.left.left
      rw [correctFindPrev] at h_aux_prev
      by_cases h_empty_cluster : isEmpty (clusters (high u x))
      · simp
        simp [h_empty_cluster]
        exact Or.elim h_aux_prev
          (fun res_exists =>
            Exists.elim res_exists
              (fun res res_correct => by
                rw [←res_correct.left]
                simp
                by_cases h_empty_next : isEmpty (clusters res)
                · have h_not_contains_cluster := (h_aux.right.right res).mp h_empty_next
                  exact False.elim (h_not_contains_cluster res_correct.right.right.left)
                · simp [h_empty_next]
                  have h_max := getMaxReturnsMax u (clusters res) (h_summary.left.right res) (h_aux.right.left res) h_empty_next
                  exact And.intro
                    (by
                      rw [transformKeysLt]
                      rw [composeCorrectHigh, composeCorrectLow]
                      exact Or.inl res_correct.right.left)
                    (And.intro
                      (by
                        rw [contains]
                        rw [composeCorrectHigh, composeCorrectLow]
                        simp
                        exact h_max.left)
                      (fun i h_i => or_iff_not_imp_left.mpr (
                          fun i_lt => by
                            simp at i_lt
                            rw [transformKeysLt] at i_lt
                            rw [transformKeysLe]
                            rw [composeCorrectHigh, composeCorrectLow]
                            rw [contains] at h_i
                            have aux_contains_i := containsAux (vEBTree.Node h summary aux clusters) i h_aux recursive_summary h_i
                            simp at aux_contains_i
                            have aux_le := res_correct.right.right.right (high u i) aux_contains_i
                            have x_not_i : high u x ≠ high u i := byContradiction (
                              fun x_eq_i => by
                                rw [not_not] at x_eq_i
                                rw [x_eq_i] at h_empty_cluster
                                rw [h_aux.right.right (high u i)] at h_empty_cluster
                                exact False.elim (h_empty_cluster aux_contains_i)
                            )
                            simp [Ne.symm x_not_i] at i_lt
                            exact Or.elim aux_le
                              (fun x_le_i => False.elim ((lt_iff_not_le.mp i_lt) x_le_i))
                              (fun res_le_i => Or.elim (le_iff_eq_or_lt.mp res_le_i)
                                (fun res_eq_i => by
                                  simp [res_eq_i]
                                  rw [res_eq_i] at h_i
                                  have h_max_i := h_max.right (low u i) h_i
                                  simp [res_eq_i] at h_max_i
                                  exact h_max_i)
                                (fun res_lt_i => Or.inl res_lt_i)))))))
          (fun prev_none => Or.inr (by
              simp [prev_none]
              exact (fun i h_i => by
                rw [contains] at h_i
                rw [transformKeysLe]
                have aux_contains_i := containsAux (vEBTree.Node h summary aux clusters) i h_aux recursive_summary h_i
                simp at aux_contains_i
                have x_not_i : high u i ≠ high u x := byContradiction (
                  fun x_eq_i => by
                    rw [not_not] at x_eq_i
                    rw [←x_eq_i] at h_empty_cluster
                    rw [h_aux.right.right (high u i)] at h_empty_cluster
                    exact False.elim (h_empty_cluster aux_contains_i)
                )
                have h_max_aux := prev_none.right (high u i) aux_contains_i
                exact Or.inl (lt_iff_le_and_ne.mpr (And.intro h_max_aux (Ne.symm x_not_i))))))
      · simp
        simp [h_empty_cluster]
        have h_min := getMinReturnsMin u (clusters (high u x)) (h_summary.left.right (high u x)) (h_aux.right.left (high u x)) h_empty_cluster
        have h_min_contains := h_min.left
        by_cases h_min_lt : getMin! u (clusters (high u x)) h_empty_cluster < low u x
        · simp [h_min_lt]
          have h_cluster_same := ih (clusters (high u x)) (low u x) (h_aux.right.left (high u x)) (h_summary.left.right (high u x))
          rw [correctFindPrev] at h_cluster_same
          exact Or.elim (h_cluster_same)
            (fun prev_exists => Exists.elim prev_exists (
              fun res res_correct => Or.inl (by
                simp [←res_correct.left]
                exact And.intro
                  (by
                    rw [transformKeysLt]
                    rw [composeCorrectHigh, composeCorrectLow]
                    exact Or.inr (And.intro rfl (res_correct.right.left)))
                  (And.intro
                    (by
                      rw [contains]
                      rw [composeCorrectHigh, composeCorrectLow]
                      exact res_correct.right.right.left)
                    (fun i h_i => or_iff_not_imp_left.mpr (
                      fun x_lt_i => by
                        simp at x_lt_i
                        rw [transformKeysLe]
                        rw [composeCorrectHigh, composeCorrectLow]
                        rw [transformKeysLt] at x_lt_i
                        by_cases high_x_lt_i : high u i < high u x
                        · exact Or.inl high_x_lt_i
                        · simp [high_x_lt_i] at x_lt_i
                          simp [x_lt_i.left]
                          simp [←x_lt_i.left] at res_correct
                          rw [contains] at h_i
                          exact Or.elim (res_correct.right.right.right (low u i) h_i)
                            (fun low_i_le_x => False.elim ((lt_iff_not_le.mp x_lt_i.right) low_i_le_x))
                            (fun res_le_i => res_le_i)))))))
            (fun prev_empty =>
              have prev_le := prev_empty.right (getMin! u (clusters (high u x)) h_empty_cluster) h_min_contains
              False.elim (lt_iff_not_le.mp h_min_lt prev_le))
        · simp [h_min_lt]
          simp at h_min_lt
          exact Or.elim h_aux_prev
            (fun aux_next_exists => Exists.elim aux_next_exists (
              fun res res_correct => by
                simp [←res_correct.left]
                by_cases h_cluster_empty : isEmpty (clusters res)
                · have aux_not_contains_res := (h_aux.right.right res).mp h_cluster_empty
                  exact False.elim (aux_not_contains_res res_correct.right.right.left)
                · simp [h_cluster_empty]
                  have h_max := getMaxReturnsMax u (clusters res) (h_summary.left.right res) (h_aux.right.left res) h_cluster_empty
                  exact And.intro
                    (by
                      rw [transformKeysLt]
                      rw [composeCorrectHigh, composeCorrectLow]
                      exact Or.inl (res_correct.right.left))
                    (And.intro
                      (by
                        rw [contains]
                        rw [composeCorrectHigh, composeCorrectLow]
                        exact h_max.left)
                      (fun i h_i => or_iff_not_imp_left.mpr (
                        fun x_lt_i => by
                          simp at x_lt_i
                          rw [transformKeysLe]
                          rw [transformKeysLt] at x_lt_i
                          rw [composeCorrectHigh, composeCorrectLow]
                          have aux_contains_i := containsAux (vEBTree.Node h summary aux clusters) i h_aux recursive_summary h_i
                          simp at aux_contains_i
                          have aux_le := res_correct.right.right.right (high u i) aux_contains_i
                          rw [contains] at h_i
                          exact Or.elim aux_le
                            (fun high_i_le_x => Or.elim x_lt_i
                              (fun high_x_lt_i => False.elim ((lt_iff_not_le.mp high_x_lt_i) high_i_le_x))
                              (fun high_x_eq_i => by
                                simp [←high_x_eq_i.left] at h_min
                                simp [←high_x_eq_i.left] at h_min_lt
                                have h_min_i := h_min.right (low u i) h_i
                                have low_i_le_x := le_trans h_min_lt h_min_i
                                exact False.elim ((lt_iff_not_le.mp high_x_eq_i.right) low_i_le_x)))
                            (fun res_le_i => Or.elim (le_iff_eq_or_lt.mp res_le_i)
                              (fun res_eq_i => Or.inr (
                                And.intro
                                  res_eq_i
                                  (by
                                    nth_rw 1 [res_eq_i] at h_i
                                    exact h_max.right (low u i) h_i)))
                              (fun res_lt_i => Or.inl res_lt_i)))))))
            (fun aux_prev_none => by
              simp [aux_prev_none.left]
              exact (fun i h_i => by
                rw [transformKeysLe]
                rw [contains] at h_i
                have aux_contains_i := containsAux (vEBTree.Node h summary aux clusters) i h_aux recursive_summary h_i
                simp at aux_contains_i
                have aux_le := aux_prev_none.right (high u i) aux_contains_i
                exact Or.elim (le_iff_eq_or_lt.mp aux_le)
                  (fun i_eq_x => by
                    simp [←i_eq_x] at h_i
                    have h_min_le := h_min.right (low u i) h_i
                    simp [i_eq_x]
                    exact le_trans h_min_lt h_min_le)
                  (fun i_lt_x => Or.inl i_lt_x)))
