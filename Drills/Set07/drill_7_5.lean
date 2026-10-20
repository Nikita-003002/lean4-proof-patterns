-- Q: Let f : ℝ → ℝ be a function such that 2f(x) + f(-x) = 3x for all real numbers x. Prove that for all x ∈ ℝ, f(x) = 3x.

import Mathlib

theorem Drill_7_5 (f : ℝ → ℝ) (h : ∀ x, 2 * f x + f (-x) = 3 * x) : ∀ x, f x = 3 * x := by
  intro x
  have h₀ := h (x)
  have h₁ := h (-x)
  norm_num at h₁
  linarith
