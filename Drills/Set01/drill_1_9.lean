-- Q: Let x and y be real numbers such that x ≥ 1 and y ≥ 1. Prove that x + y ≤ x*y + 1.

import Mathlib

theorem Drill_1_9 (x y : ℝ) (h₀: 1 ≤ x ∧ 1 ≤ y): x + y ≤ x * y + 1 := by
  nlinarith
