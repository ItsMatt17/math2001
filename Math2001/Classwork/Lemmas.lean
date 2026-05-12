
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


open Int

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
#check Odd
#check Even
#check even_or_odd
#check Int.not_dvd_of_exists_lt_and_lt

#check le_of_dvd
#check Int.ModEq.neg
#check Int.ModEq.mul
-- #check Int.ModEq.pow_two
#check Int.ModEq.refl

-- Chapter #4
#check not_prime
#check sq_le_sq'




end
