/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init


example : Reflexive ((·:ℕ) ∣ ·) := by
  dsimp [Reflexive]
  intro x
  use 1
  ring


example : ¬ Symmetric ((·:ℕ) ∣ ·) := by
  dsimp [Symmetric]
  push_neg
  use 1, 2
  constructor
  · use 2
    numbers
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 0
    constructor
    · numbers
    · numbers


example : AntiSymmetric ((·:ℕ) ∣ ·) := by
  have H : ∀ {m n}, m = 0 → m ∣ n → m = n
  · intro m n h1 h2
    obtain ⟨k, hk⟩ := h2
    calc m = 0 := by rw [h1]
      _ = 0 * k := by ring
      _ = m * k := by rw [h1]
      _ = n := by rw [hk]
  dsimp [AntiSymmetric]
  intro x y h1 h2
  obtain hx | hx := Nat.eq_zero_or_pos x
  · apply H hx h1
  obtain hy | hy := Nat.eq_zero_or_pos y
  · have : y = x := by apply H hy h2
    rw [this]
  apply le_antisymm
  · apply Nat.le_of_dvd hy h1
  · apply Nat.le_of_dvd hx h2


example : Transitive ((·:ℕ) ∣ ·) := by
  dsimp [Transitive]
  intro a b c hab hbc
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hbc
  use k * l
  calc c = b * l := by rw [hl]
    _ = (a * k) * l := by rw [hk]
    _ = a * (k * l) := by ring


example : Reflexive ((·:ℝ) = ·) := by
  dsimp [Reflexive]
  intro x
  ring

example : Symmetric ((·:ℝ) = ·) := by
  dsimp [Symmetric]
  intro x y h
  rw [h]

example : AntiSymmetric ((·:ℝ) = ·) := by
  dsimp [AntiSymmetric]
  intro x y h1 h2
  rw [h1]

example : Transitive ((·:ℝ) = ·) := by
  dsimp [Transitive]
  intro x y z h1 h2
  rw [h1, h2]


section
local infix:50 "∼" => fun (x y : ℝ) ↦ (x - y) ^ 2 ≤ 1

example : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  intro x
  calc (x - x) ^ 2 = 0 := by ring
    _ ≤ 1 := by numbers

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h
  calc (y - x) ^ 2 = (x - y) ^ 2 := by ring
    _ ≤ 1 := by rel [h]

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1, 1.1
  constructor
  · numbers
  constructor
  · numbers
  · numbers

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 1.9, 2.5
  constructor
  · numbers
  constructor
  · numbers
  · numbers

end


section

inductive Hand
  | rock
  | paper
  | scissors

open Hand


@[reducible] def r : Hand → Hand → Prop
  | rock, rock => False
  | rock, paper => True
  | rock, scissors => False
  | paper, rock => False
  | paper, paper => False
  | paper, scissors => True
  | scissors, rock => True
  | scissors, paper => False
  | scissors, scissors => False

local infix:50 " ≺ " => r


example : ¬ Reflexive (· ≺ ·) := by
  dsimp [Reflexive]
  push_neg
  use rock
  exhaust

example : ¬ Symmetric (· ≺ ·) := by
  dsimp [Symmetric]
  push_neg
  use rock, paper
  exhaust

example : AntiSymmetric (· ≺ ·) := by
  dsimp [AntiSymmetric]
  intro x y
  cases x <;> cases y <;> exhaust

example : ¬ Transitive (· ≺ ·) := by
  dsimp [Transitive]
  push_neg
  use rock, paper, scissors
  exhaust

end

/-! # Exercises -/


example : ¬ Symmetric ((·:ℝ) < ·) := by
  dsimp[Symmetric]
  push_neg
  use 0, 1
  constructor <;> numbers

section
local infix:50 "∼" => fun (x y : ℤ) ↦ x ≡ y [ZMOD 2]

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp[AntiSymmetric]
  push_neg
  use 2, 2 + 2 * 1
  constructor
  · extra
  · constructor
    · extra
    · numbers

end


section
inductive Little
  | meg
  | jo
  | beth
  | amy
  deriving DecidableEq

open Little

@[reducible] def s : Little → Little → Prop
  | meg, meg => True
  | meg, jo => True
  | meg, beth => True
  | meg, amy => True
  | jo, meg => True
  | jo, jo => True
  | jo, beth => True
  | jo, amy => False
  | beth, meg => True
  | beth, jo => True
  | beth, beth => False
  | beth, amy => True
  | amy, meg => True
  | amy, jo => False
  | amy, beth => True
  | amy, amy => True

local infix:50 " ∼ " => s


example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp[Reflexive]
  push_neg
  use beth
  exhaust


example : Symmetric (· ∼ ·) := by
  dsimp[Symmetric]
  intro x y
  cases x <;> cases y <;> exhaust

example : ¬ Symmetric (· ∼ ·) := by
  sorry

example : AntiSymmetric (· ∼ ·) := by
  sorry

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp[AntiSymmetric]
  push_neg
  use jo, meg
  exhaust

example : Transitive (· ∼ ·) := by
  dsimp[Transitive]
  intro x y z
  sorry

example : ¬ Transitive (· ∼ ·) := by
  sorry
end


section
local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp[Reflexive]
  push_neg
  use 5
  intro h
  have h1 : 5 ≡ 0 [ZMOD 5] := by
    calc
      5 = 0 + 5 * 1 := by ring
      _ ≡ 0 [ZMOD 5] := by extra

  have h2: 5 ≡ 1 [ZMOD 5] := by
    calc
      5 ≡ 5 + 1 [ZMOD 5] := by rel[h]
      _ = 1 + 5 * 1 := by ring
      _ ≡ 1 [ZMOD 5] := by extra
  have H :=
    calc
      0 ≡ 5 [ZMOD 5] := by rel[h1]
      _ ≡ 1 [ZMOD 5] := by rel[h2]
  numbers at H

example : Symmetric (· ∼ ·) := by
  sorry

example : ¬ Symmetric (· ∼ ·) := by
  dsimp[Symmetric]
  push_neg
  use 14, 15
  constructor
  · numbers
  · intro h1
    have h2 : 14 ≡ 4 [ZMOD 5] := by
      calc 14 = 4 + 5 * 2 := by ring
      _ ≡ 4 [ZMOD 5] := by extra

    have h3 : 14 ≡ 1 [ZMOD 5] := by
      calc 14 ≡ 15 + 1 [ZMOD 5] := by rel[h1]
      _ = 1 + 5 * 3 := by ring
      _ ≡ 1 [ZMOD 5] := by extra

    have H :=
      calc 1 ≡ 14 [ZMOD 5] := by rel[h3]
        _ ≡ 4 [ZMOD 5] := by rel[h2]
    numbers at H


example : AntiSymmetric (· ∼ ·) := by
  sorry

example : ¬ AntiSymmetric (· ∼ ·) := by
  sorry
example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  sorry

end


section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp[Reflexive]
  push_neg
  use 1
  numbers

example : Symmetric (· ∼ ·) := by
  dsimp[Symmetric]
  intro x y h

  have h2 : x + y = y + x := by ring
  rw[h2] at h
  exact h

example : ¬ Symmetric (· ∼ ·) := by
  sorry

example : AntiSymmetric (· ∼ ·) := by
  sorry

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp[AntiSymmetric]
  push_neg
  use 0, 3 * 1
  constructor
  · extra
  · constructor
    · extra
    · numbers


example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp[Transitive]
  push_neg
  use 1, 2, 4

  constructor
  · calc
      1 + 2 = 0 + 3 * 1 := by ring
      _ ≡ 0 [ZMOD 3] := by extra
  · constructor
    · calc
        2 + 4 = 0 + 3 * 2 := by ring
        _ ≡ 0 [ZMOD 3] := by extra
    · intro h
      have h2 :=
        calc
          1 + 4 = 2 + 3 * 1 := by ring
          _ ≡ 2 [ZMOD 3] := by extra

      have H :=
        calc
        2 ≡ 1 + 4 [ZMOD 3] := by rel[h2]
        _ ≡ 0 [ZMOD 3] := by rel[h]
      numbers at H
end

example : Reflexive ((· : Set ℕ) ⊆ ·) := by
  dsimp[Reflexive]
  intro x
  dsimp[Set.subset_def]
  exhaust

example : ¬ Reflexive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Symmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp[Symmetric]
  push_neg
  use {1}, {1, 2}
  dsimp[Set.subset_def]
  constructor
  · intro x
    exhaust
  · push_neg
    use 2
    exhaust

example : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp[AntiSymmetric]
  intro a b h1 h2
  ext x
  constructor
  · apply h1
  · apply h2


example : ¬ AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Transitive ((· : Set ℕ) ⊆ ·) := by
  dsimp[Transitive]
  intro x y z h1 h2
  dsimp[Set.subset_def]
  intro a h3
  apply h1 at h3
  apply h2 at h3
  exact h3


example : ¬ Transitive ((· : Set ℕ) ⊆ ·) := by
  sorry

section
local infix:50 "≺" => fun ((x1, y1) : ℝ × ℝ) (x2, y2) ↦ (x1 ≤ x2 ∧ y1 ≤ y2)

example : Reflexive (· ≺ ·) := by
  dsimp[Reflexive]
  intro ⟨a, b⟩
  dsimp
  constructor <;> rfl

example : ¬ Reflexive (· ≺ ·) := by
  sorry

example : Symmetric (· ≺ ·) := by
  sorry

example : ¬ Symmetric (· ≺ ·) := by
  dsimp[Symmetric]
  push_neg
  use 0, 1
  dsimp
  constructor
  · constructor <;> numbers
  · left
    numbers

example : AntiSymmetric (· ≺ ·) := by
  dsimp[AntiSymmetric]
  intro ⟨a, b⟩ ⟨c, d⟩
  dsimp
  intro ⟨h1, h2⟩ ⟨h3, h4⟩
  constructor
  · apply le_antisymm h1 h3
  · apply le_antisymm h2 h4


example : ¬ AntiSymmetric (· ≺ ·) := by
  sorry

example : Transitive (· ≺ ·) := by
  dsimp[Transitive]
  intro ⟨x1, y1⟩ ⟨x2, y2⟩ ⟨x3, y3⟩
  dsimp
  intro ⟨h1, h2⟩ ⟨h3, h4⟩

  constructor
  · calc
      x1 ≤ x2 := by rel[h1]
      _ ≤ x3 := by rel[h3]
  · calc
      y1 ≤ y2 := by rel[h2]
      _ ≤ y3 := by rel[h4]


example : ¬ Transitive (· ≺ ·) := by
  sorry

end
