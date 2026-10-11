-- Q: Suppose x and y are real numbers satisfying |x + 1| < 2 and |y - 3| < 4. Prove that if x > 0, then x ≥ 5.

import Mathlib

theorem Drill_3_2 (x y : ℝ) (h₀: |x + 1| < 2 ∧ |y - 3| < 4) : x + y < 8 := by
  rw [abs_lt, abs_lt] at h₀
  linarith
