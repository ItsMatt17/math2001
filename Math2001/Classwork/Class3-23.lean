-- Logical Equivalences
import Mathlib.Data.Real.Basic
import Library.Basic
import Mathlib.Tactic.GCongr

math2001_init


example {P  Q : Prop} (h1: P ∨ Q) (h2: ¬Q) : P := by
  obtain ha | hb := h1
  · exact ha
  · contradiction


example {P Q R : Prop} : (P ∧ (Q ∨ R)) ⇔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro ha
    obtain ha | ha := ha
    obtain ⟨hp, hq⟩ := ha
    constructor
    · exact hp
    · left
      exact hq

    obtain ⟨hp, hq⟩ := ha
    constructor
    · exact hp
    · right
      exact hq

  · intro ha
    obtain ⟨hp, hq⟩ := ha
    · obtain hq | hr := hq
      · left
        exact ⟨hp, hq⟩
      · right
        exact ⟨hp, hr⟩


example {P : Prop} : (P ∧ P) ⇔ P := by
  constructor
  · intro h1
    constructor
    · exact h1
    · exact h1

  · intro h2
    obtain ⟨h2', h2⟩ := h2
    · exact h2

/-
  Law of the excluded middle
  Def: For some `k` ∈ ℕ is superpowered
  if ∀ `n` ∈ ℕ the numbers k ^ (k ^ n) + 1 is prime

  Ex: 0 ^ (0 ^ 0) + 1 = 1
  Ex: 0 ^ (0 ^ 1) + 1 = 2
  Ex: 0 ^ (0 ^ 2) + 1 = 2
  1 is not a prime number so, not superpowered

  Ex: 1 ^ (1 ^ 0) + 1 = 2
  Ex 1 ^ (1 ^ 1) + 1 = 2
  ...
  It is superpowered...

  Prove ∃ `k` ∈ ℕ st `k` is superpowered, but k + 1 is not

  `k` = 1 is superpowered

  But... `k` = 2 is NOT superpowered


-/
