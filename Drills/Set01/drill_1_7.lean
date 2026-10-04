-- Q: Suppose x and S are real numbers such that S = 19 + |x| and S is strictly less than 25. Prove that 19 < 25 and |x| < 6.

import Mathlib

theorem Drill_1_7 (x S : ℝ) (h₀: S = 19 + |x|) (h₁: S < 25) : 19 ≤ S ∧ |x| < 6 := by
  constructor
  · linarith [abs_nonneg x]
  · linarith
