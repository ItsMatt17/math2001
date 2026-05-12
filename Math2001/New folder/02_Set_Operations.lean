/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

open Set



example (t : ℝ) : t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} := by
  dsimp
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]


example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
  -- and much, much more
    · sorry
    · sorry
  · sorry


example : {2, 1} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  exhaust


example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := by
  dsimp [Set.subset_def]
  intro t h
  obtain ⟨(h1 | h1), h2⟩ := h
  · have :=
    calc (-2) ^ 2 = t ^ 2 := by rw [h1]
      _ = 9 := by rw [h2]
    numbers at this
  · addarith [h1]


example : {n : ℕ | 4 ≤ n} ∩ {n : ℕ | n < 7} ⊆ {4, 5, 6} := by
  dsimp [Set.subset_def]
  intro n h
  obtain ⟨h1, h2⟩ := h
  interval_cases n <;> exhaust


namespace Int
example : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := by
  ext n
  dsimp
  rw [odd_iff_not_even]
end Int


example (x : ℤ) : x ∉ ∅ := by
  dsimp
  exhaust

example (U : Set ℤ) : ∅ ⊆ U := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := hx
    have :=
    calc 1 ≡ x [ZMOD 5] := by rel [hx1]
      _ ≡ 2 [ZMOD 5] := by rel [hx2]
    numbers at this
  · intro hx
    contradiction


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  suffices ¬(x ≡ 1 [ZMOD 5] ∧ x ≡ 2 [ZMOD 5]) by exhaust
  intro hx
  obtain ⟨hx1, hx2⟩ := hx
  have :=
  calc 1 ≡ x [ZMOD 5] := by rel [hx1]
    _ ≡ 2 [ZMOD 5] := by rel [hx2]
  numbers at this


example (x : ℤ) : x ∈ univ := by dsimp

example (U : Set ℤ) : U ⊆ univ := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} = univ := by
  ext t
  dsimp
  suffices -1 < t ∨ t < 1 by exhaust
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]

/-! # Exercises -/


macro "check_equality_of_explicit_sets" : tactic => `(tactic| (ext; dsimp; exhaust))


example : {-1, 2, 4, 4} ∪ {3, -2, 2} = {-1, 2, 4, 3, -2} := by check_equality_of_explicit_sets

example : {0, 1, 2, 3, 4} ∩ {0, 2, 4, 6, 8} = {0, 2, 4} := by
  check_equality_of_explicit_sets

example : {1, 2} ∩ {3} = ∅ := by check_equality_of_explicit_sets

example : {3, 4, 5}ᶜ ∩ {1, 3, 5, 7, 9} = {1, 7, 9} := by
  check_equality_of_explicit_sets

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp[Set.subset_def]
  intro a ha
  constructor
  · obtain ⟨k, hk⟩ := ha
    have H : a = 10 * k + 7 := by addarith[hk]
    calc
      a = 10 * k + 7 := by rw[H]
      _ = 1 + 2 * ((5 *k) + 3) := by ring
      _ ≡ 1 + 2 * ((5 * k) + 3) [ZMOD 2] := by extra
      _ ≡ 1 [ZMOD 2] := by extra
  · obtain ⟨k, hk⟩ := ha
    have H : a = 10 * k + 7 := by addarith[hk]

    calc
      a = 10 * k + 7 := by rw[H]
      _ = 2 + 5 * (2 * k + 1) := by ring
      _ ≡ 2 + 5 * (2 * k + 1) [ZMOD 5] := by extra
      _ ≡ 2 [ZMOD 5] := by extra


example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp[Set.subset_def]
  intro a h1
  obtain ⟨⟨k, h1⟩ ,⟨r,h2⟩⟩ := h1

  use (5 * r - 3 * k)
  calc
    a = 5 * (5 * a) - 8 * (3 * a):= by ring
    _ = 5 * 5 * (8 * r) - 8 * (3 * (5 * k)) := by rw[h1, h2]
    _ = 40 * (5 * r - 3 * k) := by ring



example : {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  dsimp[Set.subset_def]
  intro a ha

  obtain ⟨k, ha1⟩  | ⟨k, ha2⟩  := ha
  · intro h
    obtain ⟨j, h1⟩ | ⟨j, h1⟩  := Int.even_or_odd k
    · -- k is even
      have :=
        calc
          1 ≡ a ^ 2 [ZMOD 6] := by rel[h]
          _ = (3 * (2 * j)) ^ 2 := by rw[ha1, h1]
          _ = 6 * (6 * j ^ 2) := by ring
          _ ≡ 0 [ZMOD 6] := by extra
      numbers at this
    · -- k is odd
      have :=
        calc
          1 ≡ a ^ 2 [ZMOD 6] := by rel[h]
          _ = (3 * (2 * j + 1)) ^ 2 := by rw[ha1, h1]
          _ = 3 + 6 * (6 * j ^ 2 + 6 * j + 1) := by ring
          _ ≡ 3 [ZMOD 6] := by extra
      numbers at this

  · intro h

    have h1: a ≡ 2 * k [ZMOD 6] := by
      calc
        a = 2 * k := by rw[ha2]
        _ ≡ 2 * k [ZMOD 6] := by extra

    sorry




def SizeAtLeastTwo (s : Set X) : Prop := ∃ x1 x2 : X, x1 ≠ x2 ∧ x1 ∈ s ∧ x2 ∈ s
def SizeAtLeastThree (s : Set X) : Prop :=
  ∃ x1 x2 x3 : X, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 ∧ x1 ∈ s ∧ x2 ∈ s ∧ x3 ∈ s

example {s t : Set X} (hs : SizeAtLeastTwo s) (ht : SizeAtLeastTwo t)
    (hst : ¬ SizeAtLeastTwo (s ∩ t)) :
    SizeAtLeastThree (s ∪ t) := by
  sorry
