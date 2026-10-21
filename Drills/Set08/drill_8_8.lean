-- Q:  Let x be a real number such that x ≥ 0. Prove that (√x + 1)^2 = x + 2√x + 1.

import Mathlib

theorem Drill_8_8 (x : ℝ) (h₀: 0 ≤ x) : (√x + 1) ^ 2 = x + 2 * √x + 1 := by
  ring_nf
  rw [Real.sq_sqrt h₀]
