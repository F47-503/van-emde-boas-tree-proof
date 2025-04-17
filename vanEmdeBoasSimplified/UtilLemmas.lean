import Mathlib.Tactic
import vanEmdeBoasSimplified.Defs

open Classical

--we can get integer division and modulo parts of sqrt-decomposition
theorem decompDivMod (u : Nat) (x : Fin (2 ^ 2 ^ (u + 1))) :
  (2 ^ 2 ^ u) * (high u x).val + (low u x).val = x.val := by
  exact Nat.div_add_mod x (2 ^ 2 ^ u)

--if parts of two sqrt-decompositions are equal, originals are equal
theorem eqDivMod (u : Nat) (x y : Fin (2 ^ 2 ^ (u + 1))) (hdiv : high u x = high u y) (hmod : low u x = low u y) :
  x = y := by
  have h := decompDivMod u x
  rw [hdiv, hmod] at h
  rw [decompDivMod u y] at h
  rw [eq_comm] at h
  exact Fin.eq_of_val_eq h

--integer division part from combination is itself
theorem composeCorrectHigh (u : Nat) (a b : Fin (2 ^ 2 ^ u)) :
  high u (compose u a b) = a := by
  rw [compose]
  rw [high]
  apply Fin.eq_of_val_eq
  simp
  have ha : (a.val * 2 ^ 2 ^ u) % 2 ^ 2 ^ u = 0 := Nat.mul_mod_left a.val (2 ^ 2 ^ u)
  have hb : b.val % 2 ^ 2 ^ u = b.val := Nat.mod_eq_of_lt b.isLt
  rw [Nat.add_div (Nat.pow_pos zero_lt_two)]
  rw [ha, hb]
  simp
  by_cases h_big : 2 ^ 2 ^ u ≤ b.val
  · exact False.elim ((Nat.not_le_of_lt b.isLt) h_big)
  · simp [h_big]

--modulo part from combination is itself
theorem composeCorrectLow (u : Nat) (a b : Fin (2 ^ 2 ^ u)) :
  low u (compose u a b) = b := by
  rw [compose]
  rw [low]
  apply Fin.eq_of_val_eq
  simp
  exact Nat.mod_eq_of_lt b.isLt

--rephrase less-than using sqrt-decomposition
theorem compareKeysLt (u : Nat) (a b : Fin (2 ^ 2 ^ (u + 1))) (h : a < b):
  high u a < high u b ∨ high u a = high u b ∧ low u a < low u b := by
    have ha := decompDivMod u a
    have hb := decompDivMod u b
    rw [Fin.lt_def] at h
    rw [←ha, ←hb] at h
    by_cases h_eq : high u a = high u b
    · simp [h_eq]
      rw [h_eq] at h
      rw [Nat.add_lt_add_iff_left] at h
      rw [←Fin.lt_def] at h
      exact h
    · simp [h_eq]
      have pow2 : 0 < 2 ^ 2 ^ u := pow_pos zero_lt_two (2 ^ u)
      have pow2a : 2 ^ 2 ^ u * (high u a).val ≤ 2 ^ 2 ^ u * (high u a).val + (low u a).val := by
        linarith
      have pow2b : 2 ^ 2 ^ u * (high u b).val + (low u b).val < 2 ^ 2 ^ u * ((high u b).val + 1) := by
        ring_nf
        rw [Nat.add_lt_add_iff_left]
        exact (low u b).isLt
      have h_pow := Nat.lt_trans (Nat.lt_of_le_of_lt pow2a h) pow2b
      rw [Nat.mul_lt_mul_left pow2] at h_pow
      rw [Nat.lt_succ_iff] at h_pow
      rw [Fin.ext_iff] at h_eq
      exact Nat.lt_of_le_of_ne h_pow h_eq

--rephrase less-equal using sqrt-decomposition
theorem compareKeysLe (u : Nat) (a b : Fin (2 ^ 2 ^ (u + 1))) (h : a ≤ b):
  high u a < high u b ∨ high u a = high u b ∧ low u a ≤ low u b := by
    have ha := decompDivMod u a
    have hb := decompDivMod u b
    rw [Fin.le_def] at h
    rw [←ha, ←hb] at h
    by_cases h_eq : high u a = high u b
    · simp [h_eq]
      rw [h_eq] at h
      rw [Nat.add_le_add_iff_left] at h
      rw [←Fin.le_def] at h
      exact h
    · simp [h_eq]
      have pow2 : 0 < 2 ^ 2 ^ u := pow_pos zero_lt_two (2 ^ u)
      have pow2a : 2 ^ 2 ^ u * (high u a).val ≤ 2 ^ 2 ^ u * (high u a).val + (low u a).val := by
        linarith
      have pow2b : 2 ^ 2 ^ u * (high u b).val + (low u b).val < 2 ^ 2 ^ u * ((high u b).val + 1) := by
        ring_nf
        rw [Nat.add_lt_add_iff_left]
        exact (low u b).isLt
      have h_pow := Nat.lt_of_le_of_lt (Nat.le_trans pow2a h) pow2b
      rw [Nat.mul_lt_mul_left pow2] at h_pow
      rw [Nat.lt_succ_iff] at h_pow
      rw [Fin.ext_iff] at h_eq
      exact Nat.lt_of_le_of_ne h_pow h_eq

--iff property on less-equal using sqrt-decomposition
theorem transformKeysLe (u : Nat) (a b : Fin (2 ^ 2 ^ (u + 1))) :
  a ≤ b ↔ high u a < high u b ∨ high u a = high u b ∧ low u a ≤ low u b :=
    Iff.intro
      (fun h => compareKeysLe u a b h)
      (fun cond => byContradiction (
        fun b_lt => by
          simp at b_lt
          have hb := compareKeysLt u b a b_lt
          exact Or.elim hb
            (fun a_lt_b => Or.elim cond
              (fun b_lt_a => (lt_asymm a_lt_b) b_lt_a)
              (fun a_eq_b => by
                rw [a_eq_b.left] at a_lt_b
                exact lt_irrefl (high u b) a_lt_b))
            (fun h_r_b => Or.elim cond
              (fun a_lt_b => by
                rw [h_r_b.left] at a_lt_b
                exact lt_irrefl (high u a) a_lt_b)
              (fun h_r_a => (not_lt_of_le (h_r_a.right)) h_r_b.right))))

--iff property on less-than using sqrt-decomposition
theorem transformKeysLt (u : Nat) (a b : Fin (2 ^ 2 ^ (u + 1))) :
  a < b ↔ high u a < high u b ∨ high u a = high u b ∧ low u a < low u b :=
    Iff.intro
      (fun h => compareKeysLt u a b h)
      (fun cond => byContradiction (
        fun b_lt => by
          simp at b_lt
          have hb := compareKeysLe u b a b_lt
          exact Or.elim hb
            (fun a_lt_b => Or.elim cond
              (fun b_lt_a => (lt_asymm a_lt_b) b_lt_a)
              (fun a_eq_b => by
                rw [a_eq_b.left] at a_lt_b
                exact lt_irrefl (high u b) a_lt_b))
            (fun h_r_b => Or.elim cond
              (fun a_lt_b => by
                rw [h_r_b.left] at a_lt_b
                exact lt_irrefl (high u a) a_lt_b)
              (fun h_r_a => (not_lt_of_le (h_r_b.right)) h_r_a.right))))

--if x < 2, then x = 0 or x = 1. Technical lemma
theorem zeroOrOneLe (x : Fin (2 ^ 2 ^ 0)) : x = 0 ∨ x = 1 := by
  have h_vals : x.val = 0 ∨ x.val = 1 := by
    by_cases h₀ : x.val = 0
    · rw [h₀]
      simp
    · simp [h₀]
      exact le_antisymm
        (Nat.lt_succ.mp x.isLt)
        (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h₀))
  exact Or.elim h_vals
    (by
      simp
      exact Or.inl)
    (fun h1 => Or.inr (Fin.ext_iff.mpr (by
      simp
      exact h1)))

theorem pow2 (u : Nat) : 2 ^ u + 2 ^ u = 2 ^ (u + 1) := by
  rw [← Nat.add_sub_cancel u]
  rw [Nat.two_pow_pred_add_two_pow_pred]
  simp
  linarith
