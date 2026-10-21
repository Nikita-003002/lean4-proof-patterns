-- Q:  Let x be a real number such that x ≥ 3. Prove that √(x - 3)^2 = x - 3.

import Mathlib

theorem Drill_8_9 (x : ℝ) (h : 3 ≤ x) : √(x - 3) ^ 2 = x - 3 := by
  rw [Real.sq_sqrt (by linarith)]
