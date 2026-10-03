-- Q: For any real number x, prove that x^2 - 5 is always greater thanor equal to -5.

import Mathlib

theorem drill_1_1 (x : ℝ) : x ^ 2 - 5 ≥ -5 := by
  linarith [sq_nonneg x]
