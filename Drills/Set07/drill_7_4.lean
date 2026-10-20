-- Q: Let f : ℝ → ℝ be a function such that 2f(x) + f(1-x) = 3x for all real numbers x. Prove that f(1) = 2.

import Mathlib

theorem Drill_7_4 (f : ℝ → ℝ) (h: ∀ x, 2 * f x + f (1-x) = 3 * x) : f 1 = 2 := by
  have h₀ := h 0
  have h₁ := h 1
  norm_num at h₀ h₁
  linarith
