import Mathlib.Tactic.ring

-- Example #1

-- example  {a b : ℚ} (h1 : a - b = 4) (h2 : a*b = 1) : (a + b)^2 = 20 := by sorry

-- -- Example #2
-- example {r s : ℝ} (h1 : r + 2*s = -1) (h2 : s = 3) : (r = -7) by := sorry


-- example {a b c d e f : ℤ} (h1: a * d = b*c) (h2 : c * f = d * e)
--   : d * (a * f - b * e) = 0 := by
--   calc
--     d * (a * f - b * e) = (a * d) * f - (d * e) * b  := by ring
--     _ = b * c * f - b * c * f := by rw [← h2, h1]
--     _ = 0 := by ring


-- Example #5

-- example {a b : ℚ} (h1: a + b = 1) (h2: a * b = -1)
--   : (a - b)^2 = 5 := by
--     calc
--       (a - b)^2 = (a + b)^2 - 4 * (a * b) := by ring
--       _ = 1^2 - 4 * (-1) := by rw [h1, h2]
--       _ = 5 := by ring
