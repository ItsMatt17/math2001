/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  · -- the case `1 < m`
    have h1 := by apply Nat.le_of_dvd hp' hmp
    obtain hz | hz := by apply eq_or_lt_of_le h1
    · right
      apply hz

    have : ¬m ∣ p := by
      apply H
      · apply hm_left
      · apply hz

    contradiction



example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain hd | hd  := by apply le_or_lt 3 a
  · apply hd
  sorry


/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
    have hy := le_or_lt y 0
    obtain hya | hyb := hy
    · calc
      y ≤ 0 := hya
      _ ≤ x := by rel[hx]
    sorry



example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h : n % 5
  · have H :=
    calc 4 ≡ n ^ 2 [ZMOD 5] := by rel[hn]
      _ ≡ 0 ^ 2 [ZMOD 5] := by rel[h]
    numbers at H
  · have H :=
    calc 4 ≡ n ^ 2 [ZMOD 5] := by rel[hn]
      _ ≡ 1 ^ 2 [ZMOD 5] := by rel[h]
    numbers at H
  · left
    apply h
  · right
    apply h
  · have H :=
    calc 4 ≡ n ^ 2 [ZMOD 5] := by rel[hn]
      _ ≡ 4 ^ 2 [ZMOD 5] := by rel[h]
      _ ≡ 1 + 5 * 3 [ZMOD 5] := by numbers
      _ ≡ 1 [ZMOD 5] := by extra
    numbers at H

example : Prime 7 := by
  apply prime_test
  · numbers
  intro m hm hn
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 3
    constructor <;> numbers
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain h3' | h3' := h3
  · have hz : x = -2 := by addarith[h3']
    have H :=
    calc 1 < x := h2
      _ = -2 := by rw[hz]

    numbers at H

  · addarith[h3']



namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨ha, hb⟩ := h
  obtain hd | hd := Nat.even_or_odd p
  obtain hc | hc := eq_or_gt_of_le ha
  · left
    exact hc
