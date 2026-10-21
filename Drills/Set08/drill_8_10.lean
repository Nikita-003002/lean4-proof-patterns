-- Q: Let a and b be non-negative real numbers (0 ≤ a and 0 ≤ b). Prove the AM-GM inequality in root form: √(ab) ≤ a + b/2.

import Mathlib

theorem Drill_8_10 (a b : ℝ) (h : 0 ≤ a ∧ 0 ≤ b) : √(a * b) ≤ (a + b) / 2 := by
  rw [Real.sqrt_mul h.1]
  have h₀: (√a - √b) ^ 2 = a + b - 2 * √a * √b := by ring_nf; rw [Real.sq_sqrt h.1, Real.sq_sqrt h.2]
  have h₁: 0 ≤ a + b - 2 * √a * √b := by rw [← h₀]; positivity
  linarith
