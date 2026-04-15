/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intro a h1 h2

    have h1' : -1 ≤ a - 2 := by addarith[h1]
    have h2' : a - 2 ≤ 1 := by addarith[h2]

    have hp := sq_le_sq' h1' h2'
    have hp' : (a - 2) ^ 2 ≤ 1 := by addarith[hp]
    exact hp'

  · intro y h1
    have ha := by
      apply h1 1
      · numbers
      · numbers

    have hb := by
      apply h1 3
      · numbers
      · numbers

    have h : (y - 2) ^ 2 ≤ 0 := by
      calc
      (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring
      _ ≤ (1 + 1 - 2 ) / 2 := by rel[ha, hb]
      _ = 0 := by ring

    have h' : 0  ≤ (y - 2) ^ 2 := by
      calc
        0  ≤ 0  + (y - 2) ^ 2 := by extra
        _ = (y - 2) ^ 2 := by ring

    have H : (y - 2) ^ 2 = 0 := by apply le_antisymm h h'
    cancel 2 at H
    addarith[H]



example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  · numbers
  · intro k h
    calc
      k = (4 * k - 3 + 3) / 4 := by ring
      _ = (9 + 3) / 4 := by rw[h]
      _ = 3 := by numbers

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  · intro a
    extra

  · intro y
    intro h
    apply le_antisymm
    · apply h
    · extra

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp
  repeat constructor
  · numbers
  · constructor
    · numbers
    · use 3
      numbers

  intro y h
  obtain ⟨h1, h2, h3⟩ := h
  interval_cases y
  sorry

  -- What tactic to solve 0 = 2 without contradictions?
  -- h3 is blatantly false yet I have no clue how to state that.
