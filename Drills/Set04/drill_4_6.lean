-- Q: Let a and b be natural numbers. Suppose that (a : R) + (b : R) = 12 and (a : R) - (b : R) = 4. Prove that the natural number a equals 8.

import Mathlib

theorem Drill_4_6 (a b : ℕ) (h₀: (a : ℝ) + (b : ℝ) = 12) (h₁: (a : ℝ) - (b : ℝ) = 4) : a = 8 := by
  have h: (a: ℝ) = 8 := by linarith
  exact_mod_cast h
