/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

/-! # Homework 6

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-6,
for clearer statements and any special instructions. -/

@[autograded 4]
theorem problem1 : ¬ (∃ t : ℝ, t ≤ 5 ∧ 2 * t ≥ 12) := by
  intro ⟨k, ⟨h1, h2⟩⟩

  have H :=
  calc
    12 ≤ 2 * k := by rel[h2]
    _ ≤ 2 * 5 := by rel[h1]
  numbers at H



@[autograded 3]
theorem problem2 : ¬ (∃ x : ℝ, ∀ y : ℝ, y ≤ x) := by
  intro ⟨x, h1⟩

  have : x + 1 ≤ x := by apply h1
  have : 1 ≤ 0 := by addarith[this]
  numbers at this

@[autograded 3]
theorem problem3 (a : ℚ) : 3 * a + 2 < 11 ↔ a < 3 := by
  constructor
  · intro h1
    calc
      a = ((3 * a + 2)  - 2) / 3 := by ring
      _ < (11 - 2) / 3 := by rel[h1]
      _ = 3 := by numbers

  · intro h1
    calc
      3 * a + 2 < 3 * (3) + 2 := by rel[h1]
      _ = 11 := by numbers

@[autograded 6]
theorem problem4 (t : ℤ) : t ^ 2 + t + 3 ≡ 0 [ZMOD 5] ↔ t ≡ 1 [ZMOD 5] ∨ t ≡ 3 [ZMOD 5] := by
  constructor
  · intro ⟨k, h1⟩
    sorry


@[autograded 4]
theorem problem5 (P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P) := by
  sorry

@[autograded 5]
theorem problem6 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry
