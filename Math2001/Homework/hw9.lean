/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.InjectiveSurjective
import Library.Basic
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

open Function


/-! # Homework 9

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-9,
for clearer statements and any special instructions. -/


/- Problem 1: prove one of these, delete the other -/

@[autograded 4]
theorem problem1a : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp[Surjective]
  intro b
  use b / 2
  ring

/- Problem 2: prove one of these, delete the other -/


@[autograded 4]
theorem problem2b : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  dsimp[Surjective]
  push_neg

  use 1
  intro a
  obtain h | h := le_or_succ_le a 0
  · apply ne_of_lt
    calc 2 * a ≤ 2 * 0 := by rel[h]
      _ < 1 := by numbers

  · apply ne_of_gt
    calc 2 * a ≥ 2 * 1 := by rel[h]
      _ > 1 := by numbers


/- Problem 3: prove one of these, delete the other -/

@[autograded 4]
theorem problem3a : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  intro f hf a1 a2 hp
  dsimp at hp
  apply hf
  addarith[hp]



/- Problem 4: prove one of these, delete the other -/

@[autograded 4]
theorem problem4a : Bijective (fun (x : ℝ) ↦ 3 - 2 * x) := by
  dsimp[Bijective]
  dsimp[Injective, Surjective]
  constructor
  · -- Injective
    intro a1 a2 hf

    calc
      a1 = ((3 - 2 * a1) - 3) / - 2 := by ring
      _ = ((3 - 2 * a2) - 3) / -2 := by rw[hf]
      _ = a2 := by ring

  · -- Surjective
    intro a
    use (a - 3) / (-2)
    ring


/- Problem 5: prove one of these, delete the other -/
-- f a₁ b₁ c₁ = f a₂ b₂ c₂ -> (a1 + b1 + c1, a1 + 2b1 + 3c1) = (a2 + b2 + c2, a2, 2b2, 3c2)
@[autograded 5]
theorem problem5b :
    ¬Injective (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  dsimp[Injective]
  push_neg
  use (1, 0, 0), (0, 2, -1) -- Find using kernel (refresh)
  constructor <;> numbers



/- Problem 6: prove one of these, delete the other -/

@[autograded 4]
theorem problem6a : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r + 2 * s)) := by
  dsimp[Bijective, Injective, Surjective]
  constructor
  · intro (a1, b1) (a2, b2) hf
    dsimp at hf
    obtain ⟨h1, h2⟩ := hf
    constructor
    · rw[h1, ← h1] at h2
      addarith[h2]
    · exact h1
  · intro (a, b)
    -- 

@[autograded 4]
theorem problem6b : ¬ Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r + 2 * s)) := by
  sorry
