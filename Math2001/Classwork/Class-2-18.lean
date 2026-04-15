import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-
Lemmas Learnt
  - ne_of_lt (a < b => a ≠ b)
  - ne_of_gt (a > b => a ≠ b)
  - le_antisymm (a ≤ b ∧ a ≥ b => a = b)
  - le_or_gt _ _ 
  - Int.even_or_odd _
-/

example {y : ℤ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  calc
    y ^ 2 + 1 ≥ 1 := by extra
    _ > 0 := by numbers

example {a b : ℝ} (h1: a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm

  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := by rw[h1]

  calc
    0 ≤ a ^ 2 := by extra


example {x y : ℝ} (h1 : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain h2 | h2 := h1
  calc
    x * y + x = 1 * y + 1 := by rw[h2]
    _ = y + 1 := by ring

  calc
    x * y + x = x * -1 + x := by rw[h2]
    _ = 0 := by ring
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw[← h2]

example {a : ℝ} (h1: a ^ 2 = 0) : a = 0 := by
  sorry


example {n : ℝ} : n ^ 2 ≠ 2 := by
  sorry
