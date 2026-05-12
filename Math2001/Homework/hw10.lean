/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option quotPrecheck false


/-! # Homework 10

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-10,
for clearer statements and any special instructions. -/


/- Problem 1: prove one of these, delete the other -/

@[autograded 4]
theorem problem1a : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 6 * n ^ 2 ≥ 4 * n } := by
  dsimp[Set.subset_def]
  intro x h
  calc
    x ^ 3 - 6 * x ^ 2 = x * x * (x - 6) := by ring
    _ ≥ 10 * x * (10 - 6) := by rel[h]
    _ = 4 * x + 36 * x := by ring
    _ ≥ 4 * x := by extra


/- Problem 2: prove one of these, delete the other -/

@[autograded 3]
theorem problem2b : { t : ℝ | t ^ 2 - 3 * t + 2 = 0 } ≠ { s : ℝ | s = 2 } := by
  ext
  push_neg
  dsimp
  use 1
  left
  constructor <;> numbers

/- Problem 3: prove one of these, delete the other -/

@[autograded 3]
theorem problem3a : {1, 2, 3} ∩ {2, 3, 4} ⊆ {2, 3, 6} := by
  dsimp[Set.subset_def]
  intro x h
  obtain ⟨h1, h2⟩ := h
  obtain h1 | h1 | h1 := h1
  · obtain h2 | h2 | h2 := h2
    · left
      apply h2
    · right
      left
      apply h2
    · rw[h1] at h2
      numbers at h2
  · obtain h2 | h2 | h2 := h2
    · left
      apply h1
    · left
      apply h1
    · left
      apply h1
  · obtain h2 | h2 | h2 := h2
    · right
      left
      apply h1
    · right
      left
      apply h1
    · right
      left
      apply h1
  

/- Problem 4 -/

@[autograded 4]
theorem problem4 : { r : ℤ | r ≡ 11 [ZMOD 15] }
    = { s : ℤ | s ≡ 2 [ZMOD 3] } ∩ { t : ℤ | t ≡ 1 [ZMOD 5] } := by
  ext x
  dsimp
  constructor
  · intro h
    · constructor
      · obtain ⟨k, hx⟩ := h
        have h1: x = 15 * k + 11 := by addarith[hx]
        calc
          x = 15 * k + 11 := by rw[h1]
          _ = 3 * (5 * k + 3) + 2 := by ring
          _ ≡ 2 [ZMOD 3] := by extra
      · obtain ⟨k, hx⟩ := h
        have h1 : x = 15 * k + 11 := by addarith[hx]
        calc
          x = 15 * k + 11 := by rw[h1]
          _ = 5 * (3 * k + 2) + 1 := by ring
          _ ≡ 1 [ZMOD 5] := by extra
  · intro ⟨⟨k, h1⟩, ⟨r, h2⟩⟩
    have h1': x = 3 * k + 2 := by addarith[h1]
    have h2': x = 5 * r + 1 := by addarith[h2]

    use 2 * r - k - 1
    calc
      x - 11 = (6 * x - 5 * x) - 11 := by ring
      _ = (6 * (5 * r + 1) - 5 * (x)) - 11:= by rw[h2']
      _ = (6 * (5 * r + 1) - 5 * (3 * k + 2)) - 11 := by rw[h1']
      _ = 15 * (2 * r - k - 1) := by ring




/-! ### Problem 5 starts here -/


local infix:50 "∼" => fun (a b : ℤ) ↦ ∃ m n, m > 0 ∧ n > 0 ∧ a * m = b * n


/- Problem 5.1: prove one of these, delete the other -/

@[autograded 2]
theorem problem51a : Reflexive (· ∼ ·) := by
  dsimp[Reflexive]
  intro x
  use 1, 1
  constructor
  · numbers
  · constructor
    · numbers
    · ring

/- Problem 5.2: prove one of these, delete the other -/

@[autograded 2]
theorem problem52a : Symmetric (· ∼ ·) := by
  dsimp[Symmetric]
  intro a b
  intro ⟨m, n, ⟨h1, h2, h3⟩⟩
  use n, m
  constructor
  · apply h2
  · constructor
    · apply h1
    · rw[h3]


/- Problem 5.3: prove one of these, delete the other -/

@[autograded 2]
theorem problem53b : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp[AntiSymmetric]
  push_neg
  use 1, 2
  constructor
  use 2, 1
  constructor
  · numbers
  · constructor
    · numbers
    · ring

  constructor
  use 1, 2
  constructor
  · numbers
  · constructor
    · numbers
    · ring
  · numbers

/- Problem 5.4: prove one of these, delete the other -/

@[autograded 2]
theorem problem54a : Transitive (· ∼ ·) := by
  dsimp[Transitive]
  intro x y z
  intro ⟨m1, n1, ⟨h1, h2, h3⟩⟩
  intro ⟨m2, n2, ⟨h1', h2', h3'⟩⟩
  use m1 * m2, n1 * n2
  constructor
  · extra
  · constructor
    · extra
    · calc
      x * (m1 * m2) = x * m1 * m2 := by ring
      _ = y * n1 * m2 := by rw[h3]
      _ = y * m2 * n1 := by ring
      _ = z * n2 * n1 := by rw[h3']
      _ = z * (n1 * n2) := by ring


/-! ### Problem 6 starts here -/

infix:50 "≺" => fun ((x1, y1) : ℝ × ℝ) (x2, y2) ↦ (x1 ≤ x2 ∧ y1 ≤ y2)


/- Problem 6.1: prove one of these, delete the other -/

@[autograded 2]
theorem problem61a : Reflexive (· ≺ ·) := by
  dsimp [Reflexive]
  intro (x1, y1)
  dsimp
  constructor <;> rfl


/- Problem 6.2: prove one of these, delete the other -/


@[autograded 2]
theorem problem62b : ¬ Symmetric (· ≺ ·) := by
  dsimp[Symmetric]
  push_neg
  use 0, 1
  dsimp

  constructor
  · constructor <;> numbers
  · left
    numbers


/- Problem 6.3: prove one of these, delete the other -/

@[autograded 2]
theorem problem63a : AntiSymmetric (· ≺ ·) := by
  dsimp[AntiSymmetric]
  intro (x1, y1) (x2, y2) ⟨h1, h1'⟩ ⟨h2, h2'⟩
  dsimp at *
  constructor
  · apply le_antisymm h1 h2
  · apply le_antisymm h1' h2'


/- Problem 6.4: prove one of these, delete the other -/

@[autograded 2]
theorem problem64a : Transitive (· ≺ ·) := by
  dsimp[Transitive]
  intro (x1, y1) (x2, y2) (x3, y3) ⟨h1, h1'⟩ ⟨h2, h2'⟩
  dsimp at *
  constructor
  · calc
      x1 ≤ x2 := by rel[h1]
      _ ≤ x3 := by rel[h2]
  · calc
      y1 ≤ y2 := by rel[h1']
      _ ≤ y3 := by rel[h2']
