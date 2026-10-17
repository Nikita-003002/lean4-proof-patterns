-- Q: Let x ∈ ℝ such that x ≠ 1 and x^3 = 1. Prove x^2 + x + 1 = 0.
import Mathlib

theorem drill_5_6 (x : ℝ) (h₀ : x ≠ 1) (h₁ : x^3 = 1) : x^2 + x + 1 = 0 := by
  have h: (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination h₁
  rcases mul_eq_zero.mp h with hk | hk
  · have hk1: x = 1 := by linarith
    contradiction
  · exact hk
