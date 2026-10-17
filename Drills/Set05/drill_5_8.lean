-- Q: Let x and y be real numbers such that x + y = 6. Prove that xy ≤ 9.

import Mathlib

theorem Drill_5_8 (x y : ℝ) (h: x + y = 6): x * y ≤ 9 := by
  have hk: 4 * x * y ≤ 36 := by
    calc
      _ = (x + y)^ 2 - (x - y) ^ 2 := by nlinarith
      _ ≤ (x + y) ^ 2 := by nlinarith
      _ = 36 := by rw [h]; norm_num
  linarith
