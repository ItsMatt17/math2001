import Library.Basic
import Mathlib.Data.Real.Basic

math2001_init

open Nat


def sum : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sum n

#eval sum 0
#eval sum 1
#eval sum 2


theorem gauss_sum {n : ℕ} : 2 * sum n = n * (n + 1) := by
  simple_induction n with k IH
  · -- Base Case `n = 0`
    rw[sum]

  · -- Inductive Case
    calc
      2 * sum (k + 1) = 2 * ((k + 1) + sum (k)) := by rw[sum]
      _ = 2 * (k + 1) + 2 * (sum k) := by ring
      _ = 2 * (k + 1) +  k * (k + 1) := by rw[IH]
      _ =  (k + 1) * (k + 1 + 1) := by ring



lemma n_le_two_pow_n {n : ℕ} (hn : n ≥ 1) : n ≤ 2 ^ n := by
  induction_from_starting_point n, hn with k IH1 IH2
  · -- Base Case `n = 0`
    numbers

  · -- Inductive Case
    calc
      k + 1 ≤ k + k := by rel[IH1]
      _ ≤ 2 ^ k + 2 ^ k := by rel[IH2]
      _ = 2 ^ (k + 1) := by ring




theorem two_mul_sum_range (n : ℕ) : 2 * sumRange n = n * (n + 1) := by
  simple_induction n with k IH
  · -- Base Case
    calc
      2 * sumRange 0 = 2 * 0 := by rw[sumRange]
      _ = 0 := by ring
      _ = 0 * (0 + 1) := by ring

  · -- Inductive Case
    calc
      2 * sumRange (k + 1) = 2 * ((k + 1) + sumRange k) := by rw[sumRange]
      _ = 2 * (k + 1) + 2 * sumRange k := by ring
      _ = 2 * (k + 1) + k * (k + 1) := by rw[IH]
      _ = (k + 1) * (k + 1 + 1) := by ring


-- theorem gauss_sum_range (n : ℕ) : sumRange n = n * (n + 1) / 2 := by
--   have H := by apply two_mul_sum_range n
