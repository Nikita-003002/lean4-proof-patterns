-- Q: Let f : ℝ → ℝ be a function such that for all real number x, f(x + 1) = fx + 3. If f(0) = 5, prove that f(2) = 11.

import Mathlib

theorem Drill_7_1 (f : ℝ → ℝ) (h₀: ∀ x, f (x + 1) = f x + 3) (h₁: f 0 = 5) : f 2 = 11 := by
  have _ := h₀ 0
  have _ := h₀ 1
  norm_num at *
  linarith
