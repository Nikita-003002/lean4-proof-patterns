-- Q: et x and y be non-zero real numbers such that 1/x + 1/y = 5 and x + y = 10. Prove that xy = 2.

import Mathlib

theorem Drill_8_4 (x y : ℝ) (h₀ : x ≠ 0 ∧ y ≠ 0) (h₁ : 1 / x + 1 /y = 5) (h₂ : x + y = 10) : x * y = 2 := by
  field_simp [h₀] at h₁
  linarith
