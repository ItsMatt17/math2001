/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
    calc
      13 = 3 * k := hk
      _ ≥ 3 * 5 := by rel[h5]
    numbers at h

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n, hn⟩  := h
  obtain h4 | h5 := le_or_succ_le n 1
  · have H :=
    calc
      2 = n ^ 2 := by rw[hn]
      _ ≤ 1 ^ 2 := by rel[h4]
    numbers at H
  · have H :=
    calc
      2 = n ^ 2 := by rw[hn]
      _ ≥ 2 ^ 2 := by rel[h5]
    numbers at H

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro ha hb
    rw[Int.odd_iff_modEq] at ha
    rw[Int.even_iff_modEq] at hb

    have H :=
      calc 1 ≡ n [ZMOD 2] := by rel[ha]
      _ ≡ 0 [ZMOD 2] := by rel[hb]

    numbers at H
  · intro h
    obtain he | ho := Int.even_or_odd n
    · contradiction
    · apply ho



example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have H :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at H -- contradiction!
  · have H :=
    calc 1 ^ 2 ≡ n ^ 2 [ZMOD 3] := by rel[hn]
      _ ≡ 2 [ZMOD 3] := by rel[h]
    numbers at H

  · have H :=
    calc 2 ≡ n ^ 2 [ZMOD 3] := by rel[h]
      _ ≡ 2 ^ 2 [ZMOD 3] := by rel[hn]
      _ ≡ 1 + 3 * 1 [ZMOD 3] := by numbers
      _ ≡ 1 [ZMOD 3] := by extra

    numbers at H


example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  have h2 : b * q < b * k :=
    calc b * q < a := by rel[hq₁]
    _ = b * k := by rw[hk]
  cancel b at h2





example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · sorry
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  · sorry
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h
  obtain ⟨a, h₁, h₂⟩ := h
  have H :=
  calc
    4 ≥ a := by rel[h₁]
    _ ≥ 5 := by rel[h₂]
  numbers at H

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro h
  obtain ⟨a, h₁, h₂⟩ := h
  have H : sorry

example : ¬ Int.Even 7 := by
  intro h
  obtain ha | hb := Int.even_or_odd 7
  · rw [Int.even_iff_modEq] at *
    have H :=
    calc 0 ≡ 7 [ZMOD 2] := by rel[ha]
      _ ≡ 1 + 2 * 3 [ZMOD 2] := by numbers
      _ ≡ 1 [ZMOD 2] := by extra
    numbers at H

  rw [Int.even_iff_modEq] at h
  rw [Int.odd_iff_modEq] at hb
  have H :=
    calc 0 ≡ 7 [ZMOD 2] := by rel[h]
      _ ≡ 1 [ZMOD 2] := by rel[hb]
  numbers at H


example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  intro h
  obtain ⟨ha, hb⟩ := h
  have h' : n = 4 := by addarith[hn]

  have H :=
    calc
    10 = n ^ 2 := by rw[hb]
    _ = 4 ^ 2 := by rw[h']

  numbers at H

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  sorry


example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro h
  obtain ha | ha := by apply
  sorry

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro h
  mod_cases hn : n % 4
  · have H :=
    calc
      2 ≡ n ^ 2 [ZMOD 4] := by rel[h]
      _ ≡ 0 ^ 2 [ZMOD 4] := by rel[hn]
    numbers at H
  · have H :=
    calc
      2 ≡ n ^ 2 [ZMOD 4] := by rel[h]
      _ ≡ 1 ^ 2 [ZMOD 4] := by rel[hn]
    numbers at H
  · have H :=
    calc
      2 ≡ n ^ 2 [ZMOD 4] := by rel[h]
      _ ≡ 2 ^ 2 [ZMOD 4] := by rel[hn]
      _ ≡ 4 * 1 [ZMOD 4] := by numbers
      _ ≡ 0 [ZMOD 4] := by extra
    numbers at H

example : ¬Prime 1 := by
  intro h
  obtain ⟨ha, hb⟩ := h
  · numbers at ha

example : Prime 97 := by
  apply better_prime_test (T := 10)
  · numbers
  · numbers

  intro m h1 h2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 48
    constructor <;> numbers
  · use 32
    constructor <;> numbers
  · use 24
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 16
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 12
    constructor <;> numbers
  · use 10
    constructor <;> numbers
