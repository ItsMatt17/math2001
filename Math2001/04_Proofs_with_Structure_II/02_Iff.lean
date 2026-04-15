/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨a, ha⟩ := h
    use a
    addarith[ha]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨a, ha⟩ := h
    use a
    addarith[ha]

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have h1 :=
    calc
      (x + 3) * (x - 2) = x ^ 2 + x - 6 := by ring
      _ = 0 := by rw[h]
    obtain h1'| h1' := eq_zero_or_eq_zero_of_mul_eq_zero h1
    · left
      addarith[h1']
    · right
      addarith[h1']
  · intro h
    obtain h1 | h1 := h
    · calc
      x ^ 2 + x - 6 = (-3) ^ 2 + -3 - 6 := by rw[h1]
      _ = 0 := by numbers
    · calc
      x ^ 2 + x - 6 = 2 ^ 2 + 2 - 6 := by rw[h1]
      _ = 0 := by numbers


example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  sorry

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain hn2 | hn2 := hn2
  · use 2
    addarith[hn2]
  · use 3
    addarith[hn2]

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain hn1 | hn1 := hn1
  · use 2
    addarith[hn1]
  · use 3
    addarith[hn1]

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  intro h1
  · calc
    x = (2 * x - 1 + 1) / 2 := by ring
    _ = (11 + 1) / 2 := by rw[h1]
    _ = 6 := by numbers
  intro h1
  · calc
    2 * x - 1 = 2 * 6 - 1 := by rw[h1]
    _ = 11 := by numbers

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  intro h1
  · obtain ⟨a, ha⟩ := h1
    constructor
    · use 9 * a
      calc
        n = 9 * (n) - 8 * (n) := by ring
        _ = 9 * (63 * a) - 8 * (63 * a) := by rw[ha]
        _ = 7 * (9 * a) := by ring

    · use 7 * a
      calc
        n = 9 * (n) - 8 * (n) := by ring
        _ = 9 * (63 * a) - 8 * (63 * a) := by rw[ha]
        _ = 9 * (7 * a) := by ring
  intro h2
  obtain ⟨ha, hb⟩ := h2
  obtain ⟨a, ha'⟩ := ha
  obtain ⟨b, hb'⟩ := hb
  use 4 * b - 3 * a
  calc
    n = 7 * (4 * n) - 9 * (3 * n) := by ring
    _ = 7 * (4 * (9 * b)) - 9 * (3 * n) := by rw[hb']
    _ = 7 * (4 * (9 * b)) - 9 * (3 * (7 * a)) := by rw[ha']
    _ = 63 * (4 * b - 3 * a) := by ring



theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  intro h1
  · obtain ⟨k, hk⟩ := h1
    use k
    addarith[hk]

  intro h1
  · obtain ⟨k, hk⟩ := h1
    use k
    addarith[hk]


example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, hk⟩ := hab
  use (2 * a ^ 2 * k ^ 3 ) - a * k ^ 2 + 3 * a * k
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b = 2 * (a * k) ^ 3 - (a * k) ^ 2 + 3 * (a * k) := by rw[hk]
    _ = 2 * (a ^ 3 * k ^ 3) - (a ^ 2 * k ^ 2) + 3 * (a * k) := by ring
    _ = a * ((2 * a ^ 2 * k ^ 3 ) - a * k ^ 2 + 3 * k) := by ring


example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  sorry
