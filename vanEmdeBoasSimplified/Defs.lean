import Mathlib.Tactic

--definition of datastructure
inductive vEBTree : Nat → Type where
| Leaf : (Fin 2 → Bool) → vEBTree 0 --whether tree contains 0 and 1
| Node {u : Nat} (h : u > 0)
       (summary : Option (Fin (2 ^ 2 ^ u) × Fin (2 ^ 2 ^ u))) --min and max or empty
       (aux : vEBTree (u - 1)) --auxilary tree
       (cluster : Fin (2 ^ 2 ^(u - 1)) → vEBTree (u - 1)) --clusters
       : vEBTree u

--technical lemma about powers of two
theorem universeProd (v : Nat) : 2 ^ 2 ^ v * 2 ^ 2 ^ v = 2 ^ 2 ^ (v + 1) := by
  rw [←pow_add]
  rw [← Nat.add_sub_cancel_right v 1]
  rw [Nat.two_pow_pred_add_two_pow_pred (by linarith)]
  simp

--integer division part of sqrt-decomposition
def high (u : Nat) (x : Fin (2 ^ 2 ^ (u + 1))): Fin (2 ^ 2 ^ u) :=
  Fin.mk
    (x.val / (2 ^ 2 ^ u))
    ((Nat.div_lt_iff_lt_mul (Nat.pow_pos (zero_lt_two))).mpr (by
      rw [universeProd u]
      exact x.isLt))

--modulo part of sqrt-decomposition
def low (u : Nat) (x : Fin (2 ^ 2 ^ (u + 1))): Fin (2 ^ 2 ^ u) :=
  Fin.mk (x.val % (2 ^ 2 ^ u)) (Nat.mod_lt x.val (Nat.pow_pos zero_lt_two))

--combine quotient and remainder to integer
def compose (u : Nat) (a b : Fin (2 ^ 2 ^ u)) : Fin (2 ^ 2 ^ (u + 1)) :=
  ⟨a * 2 ^ 2 ^ u + b,
  by
    have ha : a.val ≤ 2 ^ 2 ^ u - 1 := (Nat.lt_iff_le_pred (Nat.pow_pos zero_lt_two)).mp a.is_lt
    have hb : b.val < 2 ^ 2 ^ u := b.is_lt
    exact Nat.lt_of_le_of_lt
      (Nat.add_le_add_right (Nat.mul_le_mul_right (2 ^ 2 ^ u) ha) b.val)
      (by
        rw [Nat.sub_mul]
        rw [universeProd u]
        rw [add_comm]
        have hb₁ : b.val + (2 ^ 2 ^ (u + 1) - 2 ^ 2 ^ u) < 2 ^ 2 ^ u + (2 ^ 2 ^ (u + 1) - 2 ^ 2 ^ u):= by
          exact Nat.add_lt_add_right hb (2 ^ 2 ^ (u + 1) - 2 ^ 2 ^ u)
        have pow2le : 2 ^ 2 ^ u ≤ 2 ^ (2 ^ u * 2) :=
          Nat.pow_le_pow_of_le (one_lt_two) (by
            simp)
        have pow2eq : 2 ^ 2 ^ u + (2 ^ 2 ^ (u + 1) - 2 ^ 2 ^ u) = 2 ^ 2 ^ (u + 1) := by
          ring_nf
          exact Nat.sub_add_cancel pow2le
        nth_rw 2 [←pow2eq]
        simp)⟩

--function for clusters update : update one value and keep others
def updateFin {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) (a : α) : Fin n → α :=
  fun j => if j = i then a else f j
