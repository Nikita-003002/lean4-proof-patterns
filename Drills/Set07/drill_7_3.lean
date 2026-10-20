-- Q:  Let f : ℝ → ℝ be a function such that f(x + y) = f(x) + f(y) for all x, y ∈ ℝ. Prove that for all real numbers x, f(-x) = -f(x).

import Mathlib

theorem Drill_7_3 (f : ℝ → ℝ) (h: ∀ x y : ℝ, f (x + y) = f x + f y) : ∀ x, f (-x) = - f x := by
  intro x
  have h₀ := h (-x) (x)
  have h₁ := h 0 0
  simp at h₀ h₁
  linarith
