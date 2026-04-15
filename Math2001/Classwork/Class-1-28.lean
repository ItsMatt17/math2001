import Mathlib.Tactic.ring

-- Example #7
example {a b : ℤ } (h1: a = 2 * b + 5) (h2: b = 3) :
  a = 11 := by
    calc
      a = 2 * b + 5 := by rw [h1]
      _ = 2 * (3) + 5 := by rw [h2]
      _ = 11 := by ring

-- Example #8
example {w : ℕ} (h1 : 3 * w + 1 = 4) :
  w = 1 := by
    calc
      w = ((3 * w + 1) / 3) - (1/3) := by sorry
      _ = 4 / 3 - 1/3 := by rw[h1]
      _ = 1 := by ring



-- Example #9

example {x y : ℕ} (h1 : x + y = 4) (h2: 5*x - 3*y = 4)
  : (x = 2) := by
    calc
      x = (5 * x - 3 * y + 3 * (x + y)) / 8 := by ring_nf!
      _ = (4 + 3 * 4) / 8 := by rw [h1, h2]
      _ = (16) / 8 := by ring
      _ = 2 := by ring


example {r s : ℚ} (h1 : s + 3 ≥ r) (h2: s + r ≤ 3)
  : r ≤ 3 := by
    calc
      r =
