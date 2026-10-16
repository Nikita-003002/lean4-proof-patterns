-- Q: Let x and y be real number such that x + y = 7 and xy = 10. Prove that x^2 + y^2 = 29.

import Mathlib

theorem Drill_5_1 (x y : ℝ) (h₀: x + y = 7) (h₁: x * y = 10): x ^ 2 + y ^ 2 = 29 := by
  calc
    _ = (x + y) ^ 2 - 2 * (x * y) := by ring
    _ = 29 := by rw [h₀, h₁]; norm_num
