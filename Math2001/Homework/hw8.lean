/- Copyright (c) Heather Macbeth, 2024.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import AutograderLib

macro_rules | `(tactic| gcongr_discharger) => `(tactic| numbers)
math2001_init

namespace Nat

/-! # Homework 8

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-8,
for clearer statements and any special instructions. -/


def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

@[autograded 4]
theorem problem1 (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  · -- Base Case
    rw[B]
    ring
  · -- Inductive Case
    rw[B, IH]
    ring


def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

@[autograded 4]
theorem problem2 (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k IH
  · -- Base Case
    rw[S]
    ring
  · -- Inductive Case
    rw[S, IH]
    ring


def a : ℕ → ℤ
  | 0 => 4
  | n + 1 => 3 * a n - 5

#eval a 0 ≥ 10 * 2 ^ 0
#eval a 1 ≥ 10 * 2 ^ 1
#eval a 2 ≥ 10 * 2 ^ 2
#eval a 3 ≥ 10 * 2 ^ 3
#eval a 5 ≥ 10 * 2 ^ 5

@[autograded 4]
theorem problem3 : forall_sufficiently_large (n : ℕ), a n ≥ 10 * 2 ^ n := by
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- Base Case
    repeat rw[a]
    numbers
  · -- Inductive Case
    sorry


def c : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c n

@[autograded 4]
theorem problem4 (n : ℕ) : c n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  · -- Base case #1
    rw[c]
    ring
  · -- Base Case #2
    rw[c]
    ring
  · -- Inductive Case

    calc
      c (k + 1 + 1) = 4 * c (k) := by rw[c]
      _ = 4 * (2 * 2 ^ k + (-2) ^ k) := by rw[IH1]
      _ = 2 * 2 ^ (k + 1 + 1) + (-2) ^ (k + 1 + 1) := by ring



def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

@[autograded 4]
theorem problem5 (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  · -- Base Case #1
    rw[q]
    ring
  · -- Base Case #2
    rw[q]
    ring
  · -- Inductive Case
    rw[q, IH1, IH2]
    ring

@[autograded 5]
theorem problem6 (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  have h1 := Nat.even_or_odd n
  match n with
  | k =>
    obtain h1 | h1 := h1
