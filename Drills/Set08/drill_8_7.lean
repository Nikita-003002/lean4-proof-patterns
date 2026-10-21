-- Q: For any real number x, prove that 2x/(x^2 + 1) ≤ 1.

import Mathlib

theorem Drill_8_7 (x : ℝ) : 2 * x / (x ^ 2 + 1) ≤ 1 := by
  field_simp
  linarith [sq_nonneg (x - 1)]
