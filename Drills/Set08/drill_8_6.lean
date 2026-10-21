-- Q: Let x be a strictly positive real number. Prove that 2 ≤ x + 1/x.

import Mathlib

theorem Drill_8_6 (x : ℝ) (h: 0 < x) : 2 ≤ x + 1 / x := by
  field_simp
  linarith [sq_nonneg (x - 1)]
