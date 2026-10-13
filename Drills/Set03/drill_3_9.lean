-- Q: Let x be a real number such that x^2 - 5x + 6 = 0. Prove that x = 2 or x = 3.

import Mathlib

theorem Drill_3_9 (x : ℝ) (h₀: x^2 - 5 * x + 6 = 0): x = 2 ∨ x = 3 := by
  have h_fac: (x - 2) * (x - 3) = 0 := by linarith
  rcases mul_eq_zero.mp h_fac with h | h
  · left; linarith
  · right; linarith
