-- Q: Let x and y be real numbers such that |x - 3| ≤ 2 and y = x + 5. Prove that 6 ≤ y.

import Mathlib

theorem Drill_1_8 (x y : ℝ) (h₀: |x - 3| ≤ 2) (h₁: y = x + 5): 6 ≤ y := by
  linarith [abs_le.mp h₀]
