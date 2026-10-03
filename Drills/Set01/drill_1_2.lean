-- Q: Let x be a real number. Show that 6x - 9 ≤ x^2.

import Mathlib

theorem drill_1_2 (x : ℝ) : 6 * x - 9 ≤ x ^ 2 := by
  linarith [sq_nonneg (x - 3)]
