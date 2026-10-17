-- Q: Let x be a real number such that x^2 = x + 1. Prove that x^5 = 5x + 3.

import Mathlib

theorem Drill_5_5 (x : ℝ) (h: x ^ 2 = x + 1): x ^ 5 = 5 * x + 3 := by
  linear_combination (x ^3 + x ^ 2 + 2 * x + 3) * h
