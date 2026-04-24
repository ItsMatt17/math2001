-- import Mathlib.Data.Fintype.BigOperators
-- import Library.Tactic.ModEq
import Library.Basic

math2001_init

open Nat

/-- `choose k n` is the combinatorial choice C(n, k) -/
def C: ℕ → ℕ → ℕ
  | n, 0 => 1
  | 0, k + 1 => 0
  | n + 1, k + 1 => C n k + C n (k + 1)

#eval C 0 0
#eval C 1 2
#eval C 1 1
#eval C 0 0
#eval C 2 2


theorem choose_eq_zero (n k : ℕ) (h1: n < k) : C n k = 0 := by
  match n, k with
  | 0, 0 => numbers at h1
  | 0, k + 1 => rw[C]
  | n + 1 , k + 1 =>

    have h1: n < k := by addarith[h1]
    have h2: n < k + 1 :=
      calc
        n < k := by rel[h1]
        _ < k + 1 := by extra

    have IH1 := choose_eq_zero n k h1
    have IH2 := choose_eq_zero n (k + 1) h2
    rw[C, IH1, IH2]


theorem choose_same (n : ℕ) : C n n = 1 := by
  match n with
  | 0 => rw[C]
  | n + 1 =>
    have IH := choose_same n
    have h1 : n < n + 1 := by extra
    calc
      C (n + 1) (n + 1) = C n n + C n (n + 1) := by rw[C]
      _ = 1 + C n (n + 1) := by rw[IH]
      _ = 1 + 0 := by rw[choose_eq_zero n (n + 1) h1]


theorem choose_symm (n k : ℕ) (h1 : k ≤ n) : C n k = C n (n - k) := by










theorem choose_expan (n k : ℕ) (h1 : k ≤ n) : k ! * (n - k)! * C n k = n ! := by
  match n, k with
  | 0, k =>
    have h2 : k = 0 := Nat.eq_zero_of_le_zero h1
    calc
      k ! * (0 - k)! * C 0 k = 0 ! * (0 - 0)! * C 0 0 := by rw[h2]
      _ = 0! * (0)! * C 0 0 := by ring
      _ = 1 * 1 * 1 := by rw[factorial, C]
  | n + 1, 0 =>

    calc
      0! * (n + 1 - 0)! * C (n + 1) 0 = 0! * (n + 1)! * C (n + 1) 0 := by apply add_zero
      _ = 1 * (n + 1)! * 1:= by rw[factorial, C]
      _ = (n + 1)! := by ring

  | n + 1, k + 1 =>
    have h2 : k ≤ n := by addarith[h1]
    have h3 : k ≤ n + 1 := by addarith[h1]


    have IH1 := choose_expan n k h2
    have IH2 := choose_expan (n + 1) k h3

    have h4 := Nat.add_sub_add_right n 1 k
    rw[h4]

    have H :=
    calc
      (k + 1)! * (n - k)! * C (n + 1) (k + 1) = (k + 1)! * (n - k)! * (C n k + C n (k + 1)) := by rw[C]
      _ = (k + 1) * k ! * (n - k)! * (C n k + C n (k + 1)) := by rw[factorial]
      _ = (k * k ! + k !) * (n - k)! * (C n k + C n (k + 1)) := by ring
      _ = (k * k ! + k !) * (n - k)! * C n k + (k * k ! + k !) * (n - k)! * C n (k + 1) := by ring
      _ = (n - k)! * (k * k !) * C n k + k ! * (n - k)! * C n k + (k * k ! + k !) * (n - k)! * C n (k + 1) := by ring
      _ = (n - k)! * (k * k !) * C n k + n ! + (k * k ! + k !) * (n - k)! * C n (k + 1) := by rw[IH1]
      _ = k *  (k ! * (n - k)! * C n k) + n ! + (k * k ! + k !) * (n - k)! * C n (k + 1) := by ring
      _ = k * n ! + n ! + (k * k ! + k !) * (n - k)! * C n (k + 1) := by rw[IH1]
      _ = (k + 1) * n ! + (k + 1) * k ! * (n - k)! * C n (k + 1) := by ring
      _ = (k + 1) * (n ! + k ! * (n - k)! * C n (k + 1)) := by ring



-- theorem choose_expan (n k : ℕ) (h1 : k ≤ n) : k ! * (n - k)! * C n k = n ! := by
