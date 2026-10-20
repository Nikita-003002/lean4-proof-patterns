-- Q: Let x and y be real numbers such that x + y > 10. Prove that it is not the case that both x ≤ 5 and y ≤ 5.

import Mathlib

theorem Drill_7_9 (x y : ℝ) (h: 10 < x + y) : 5 < x ∨ 5 < y := by
  by_contra! h₀
  linarith
