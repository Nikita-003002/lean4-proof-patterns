-- Q: For all real numbers a and b, prove that a^2 + b^2 is at least 2ab.

import Mathlib

theorem Drill_1_3 (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  linarith [sq_nonneg (a - b)]
