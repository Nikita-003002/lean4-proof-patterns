-- Q: Suppose x and y are real numbers such that y = 19 + |x|. Prove that y is atleast 19.

import Mathlib

theorem Drill_1_5 (x y : ℝ) (h₀: y = 19 + |x|) : 19 ≤ y := by
  linarith [abs_nonneg x]
