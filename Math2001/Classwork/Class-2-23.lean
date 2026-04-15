import Mathlib.Data.Real.Basic
import Library.Basic
import Mathlib.Tactic.GCongr

math2001_init


example {a : ℚ} (h : ∃ b, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := by rw[hb]
    _ ≥ 1 := by extra
    _ > 0 := by numbers

example {t : ℝ} (h : ∃ a, a * t < 0) : t ≠ 0 := by
  sorry

-- Different kinds of existence problems in
-- which we will produce an explicit number
example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers

example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  sorry


example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 0, 0
  numbers


-- Chapter 3: Parity & Divisibility

example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers

example : Even (-4 : ℤ) := by
  dsimp[Even]
  use -2
  numbers

example {n : ℤ} (h1: Odd (n)) : Odd (7* n - 4) := by
  sorry


example {x y : ℤ} (h1 : Odd x) (h2: Odd y) :
  Odd (x + y + 1) := by

  dsimp[Odd] at *
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2

  use k + l + 1
  calc
    x + y + 1 = (2 * k + 1) + (2 * l + 1) + 1 := by rw[hk, hl]
    _ = 2 * (k + l + 1) + 1 := by ring


example {m : ℤ} (h1: Odd m) : Even (3 * m - 5) := by
  dsimp[Odd, Even] at *
  obtain ⟨l, hl⟩ := h1

  use 3 * l - 1
  calc
    3 * m - 5 = 3 * (2 * l + 1) - 5 := by rw[hl]
    _ = 6 * l + 3 - 5 := by ring
    _ = 6 * l - 2 := by ring
    _ = 3 * l - 1 + (3 * l - 1) := by ring


example {n : ℤ} : Even (n ^ 2 + n + 4) := by
    sorry

-- a | b => ∃ c : ℤ, b = a * c

example : (11 : ℕ) ∣ 88 := by
  dsimp[(· ∣ ·)]
  use 8
  numbers

example {a b : ℤ} (h1 : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk⟩ := h1
  dsimp[(· ∣ ·)] at *

  use (a * k ^ 2 + 2 * k )

  · calc
    b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) := by rw[hk]
    _ = a * (a * k ^ 2 + 2 * k) := by ring


example : ¬(5 : ℤ) ∣ 12 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2
  constructor
  · numbers
  · numbers




example {a b : ℕ} (h1: b > 0) (h2: a ∣ b) : a > 0 := by
  sorry

