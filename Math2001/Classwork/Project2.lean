import Mathlib.Data.Nat.Basic
import Library.Basic

math2001_init


def choose' : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose' n k + choose' n (k + 1)

def factorial' : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial' n

notation:10000 n "!" => factorial' n

#eval choose' 3 0
#eval choose' 3 1
#eval choose' 3 2
#eval choose' 3 3



theorem choose_left_zero (k : ℕ) : choose' 0 (k + 1) = 0 := by rw[choose']

theorem choose_right_zero (n : ℕ) : choose' n 0 = 1 := by rw[choose']

theorem choose_gt_eq_zero (n k : ℕ) (hn : n < k) : choose' n k = 0 := by
  match n, k with
  | n, 0 =>
    have := Nat.not_lt_zero n
    contradiction
  | 0, k + 1 => apply choose_left_zero
  | n + 1, k + 1 =>
    have hk : n < k := by addarith[hn]
    have hk' : n < k + 1 :=
      calc
        n < k := hk
        _ < k + 1 := by extra

    have IH1 := choose_gt_eq_zero n k hk
    have IH2 := choose_gt_eq_zero n (k + 1) hk'
    rw[choose', IH1, IH2]

theorem choose_same (n k : ℕ) (hn : n = k) : choose' n k = 1 := by
  match n, k with
  | n, 0 => rw[hn, choose']
  | 0, k + 1 => rw[← hn, choose']
  | n + 1, k + 1 =>
    have hk: n = k := by addarith[hn]
    have IH1 := choose_same n k hk
    have hk' : n < k + 1 := by addarith[hk]
    rw[choose', IH1, choose_gt_eq_zero n (k + 1) hk']

theorem choose_expansion_factorial (n k : ℕ) (hn : k ≤ n) : choose' n k * (n - k)! * k ! = n ! := by
  match n, k with
  | 0, k =>
    have hk := Nat.eq_zero_of_le_zero hn
    rw[hk, choose', Nat.sub_zero, factorial']
  | n + 1, 0 =>
    rw[choose', Nat.sub_zero, factorial']
    ring
  | n + 1, k + 1 =>
    obtain h1 | h1  := Nat.lt_or_eq_of_le hn
    · -- `k + 1 < n + 1`
      have h2 : k ≤ n := by addarith[h1]
      have h2': k < n := by addarith[h1]

      have h3 : k + 1 ≤ n := Nat.succ_le_of_lt h2'

      have IH1 := choose_expansion_factorial n k h2
      have IH2 := choose_expansion_factorial n (k + 1) h3

      have h4 : n + 1 - (k + 1) = (n - (k + 1)) + 1 := Nat.succ_sub h3
      have h5 : (k + 1) + (n - k) = (1 + n) := by
        calc
        (k + 1) + (n - k) =  (1 + k) + (n - k) := by ring
        _ = (1 + (k + (n - k))) := by ring
        _ = (1 + n) := by rw[Nat.add_sub_cancel' h2]


      calc
        (choose' n k + choose' n (k + 1)) * (n + 1 - (k + 1))! * (k + 1)! = choose' n k  * (n + 1 - (k + 1))! * (k + 1)! + choose' n (k + 1) * (n + 1 - (k + 1))! * (k + 1)! := by ring
        _ = choose' n k * (n - k)! * (k + 1)! + choose' n (k + 1) * (n + 1 - (k + 1))! * (k + 1)! := by simp
        _ = choose' n k * (n - k)! * ((k + 1) * k !) + choose' n (k + 1) * (n + 1 - (k + 1))! * (k + 1)! := by rw[factorial']
        _ = choose' n k * (n - k)! * k ! * (k + 1)  + choose' n (k + 1) * (n + 1 - (k + 1))! * (k + 1)! := by ring
        _ = n ! * (k + 1) + choose' n (k + 1) * (n + 1 - (k + 1))! * (k + 1)! := by rw[IH1]
        _ = n ! * (k + 1) + choose' n (k + 1) * ((n - (k + 1)) + 1)! * (k + 1)! := by rw[h4]
        _ = n ! * (k + 1) + choose' n (k + 1) * (((n - (k + 1)) + 1) * (((n - (k + 1))))!) * (k + 1)! := by rw[factorial']
        _ = n ! * (k + 1) + choose' n (k + 1) * (((n - (k + 1))))! * (k + 1)! * ((n - (k + 1)) + 1) := by ring
        _ = n ! * (k + 1) + n ! * (n - (k + 1) + 1) := by rw[IH2]
        _ = n ! * ((k + 1) + (n - (k + 1) + 1)) := by ring
        _ = n ! * ((k + 1) + (n + 1 - (k + 1))) := by rw[← h4]
        _ = n ! * ((k + 1) + (n - k)) := by rw[Nat.add_sub_add_right]
        _ = n ! * (1 + n) := by rw[h5]
        _ = (n + 1) * n ! := by ring
        _ = (n + 1)! := by rw[factorial']

    · -- `k + 1 = n + 1`
      have h2: n = k := by addarith[h1]
      have h3 : n < k + 1 := by addarith[h2]

      rw[choose', choose_gt_eq_zero n (k + 1) h3, choose_same n k h2, Nat.add_zero]

      calc
        1 * (n + 1 - (k + 1))! * (k + 1)! = 1 * (n + 1 - (n + 1))! * (k + 1)! := by rw[h1]
        _ = 1 * (0)! * (k + 1)! := by rw[Nat.sub_self (n + 1)]
        _ = 1 * 1 * (k + 1)! := by rw[factorial']
        _ = (k + 1)! := by ring
        _ = (n + 1)! := by rw[h1]
