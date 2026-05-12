import Mathlib.Data.Nat.Basic
import Library.Basic
-- math2001_init MAJOR PROBLEM WITH NAT proving final theorem was impossible without removing
-- + Remove restrictions on tactics b/c the lots of problems could not be solve with ring / numbers
-- so I chose to use simp


/-- The recursive definition of `n choose k` -/
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

theorem choose_eq_zero_of_gt (n k : ℕ) (hn : n < k) : choose' n k = 0 := by
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

    have IH1 := choose_eq_zero_of_gt n k hk
    have IH2 := choose_eq_zero_of_gt n (k + 1) hk'
    rw[choose', IH1, IH2]

theorem choose_same (n k : ℕ) (hn : n = k) : choose' n k = 1 := by
  match n, k with
  | n, 0 => rw[hn, choose']
  | 0, k + 1 => rw[← hn, choose']
  | n + 1, k + 1 =>
    have hk: n = k := by addarith[hn]
    have IH1 := choose_same n k hk
    have hk' : n < k + 1 := by addarith[hk]
    rw[choose', IH1, choose_eq_zero_of_gt n (k + 1) hk']

/--
  An intermediary theorem to prove the binomal expansion to `choose n k = n! / ((n - k)! * k!)`

  -/
theorem choose_expansion_factorial (n k : ℕ) (hn : k ≤ n) : choose' n k * (n - k)! * k ! = n ! := by
  match n, k with
  | 0, k =>
    have hk := Nat.eq_zero_of_le_zero hn
    rw[hk, choose', Nat.sub_zero, factorial']
  | n + 1, 0 => rw[choose', Nat.sub_zero, factorial', Nat.mul_one, Nat.one_mul]
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
      
      rw[choose', choose_eq_zero_of_gt n (k + 1) h3, choose_same n k h2, Nat.add_zero, Nat.one_mul]

      calc
        (n + 1 - (k + 1))! * (k + 1)! = (n + 1 - (n + 1))! * (k + 1)! := by rw[h1]
        _ = (k + 1)! := by rw[Nat.sub_self (n + 1), factorial', Nat.one_mul]
        _ = (n + 1)! := by rw[h1]


theorem factorial_gt_zero (n : ℕ) : 0 < n ! := by
  simple_induction n with k IH
  · -- Base Case `0 < 0!`
    rw[factorial']
    numbers
  · -- Inductive Case
    calc
      (k + 1)! = (k + 1) * k ! := by rw[factorial']
      _ = k * k ! + k ! := by ring
      _ ≥ k ! := by extra
      _ > 0 := by rel[IH]

/-- Required to prove that I can divide by `(n - k)! * k!` -/
theorem factorial_pos_of_ge (n k : ℕ) (hn:  k ≤ n) : 0 < (n - k)! * k ! := by
  have h1: 0 < (n - k)! := factorial_gt_zero (n - k)
  have h2: 0 < k ! := factorial_gt_zero k
  extra

/-- Full `Binomal Expansion` `choose n k = n! / ((n - k)! * k!)`
    i.e this is the final product of my project.
-/
theorem choose_expansion_factorial' (n k : ℕ) (hn : k ≤ n) :
  choose' n k =  (n !) / ((n - k)! * k !) := by

  have h1 := choose_expansion_factorial n k hn
  have h2 : 0 < (n - k)! * k ! := factorial_pos_of_ge n k hn
  have h1': n ! = ((n - k)! * k !) * choose' n k := by
    calc
      n ! = choose' n k * (n - k)! * k ! := by rw[h1]
      _ = choose' n k * ((n - k)! * k !) := by rw[Nat.mul_assoc]
      _ = ((n - k)! * k !) * choose' n k  := by ring


  have h3 := (Nat.div_eq_of_eq_mul_right h2 h1')
  exact h3.symm -- .symm to reverse the equal sign
