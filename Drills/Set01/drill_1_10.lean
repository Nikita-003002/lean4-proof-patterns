-- Q: Let x be a real number amd y be a strictly positive number. Prove that (x^2 + 1)/y + |y| is strictly positive.

import Mathlib

theorem Drill_1_10 (x y : ℝ) (h₀: y > 0): 0 < (x ^ 2 + 1) /  y + |y| := by
  positivity
