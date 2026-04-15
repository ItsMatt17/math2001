
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

theorem easy : 2 + 2 = 4 :=
  rfl
#check easy


section
variable (a b : ℤ)

-- Chapter #2
#check ne_of_lt
#check ne_of_gt
#check le_antisymm
#check le_or_succ_le a 1
#check eq_zero_or_eq_zero_of_mul_eq_zero
#check abs_le_of_sq_le_sq'


-- Chapter #3
/-
  dsimp [...] → to simplify a definition
    [Odd]
    [Even]
    [Dvd.dvd]


-/
#check Odd
#check Even

-- (`n` : ℤ) : Even `n` ∨ Odd `n`
#check Int.even_or_odd

-- (a b : ℤ) (∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a
#check Int.not_dvd_of_exists_lt_and_lt

-- (m n : ℕ) (h > 0) (m | n) : n ≥ m
#check Nat.le_of_dvd


#check Int.ModEq.neg
#check Int.ModEq.mul
-- #check Int.ModEq.pow_two
#check Int.ModEq.refl

-- Chapter #4
#check not_prime
#check sq_le_sq'




end
