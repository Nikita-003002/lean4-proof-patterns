-- Q:  Let a : ℕ → ℝ be a sequence such that a₀ = 1, a₁ = 2, and a_{n+2} = a_{n+1} + a_n for all n ∈ ℕ. Prove that a₃ = 5.

import Mathlib

theorem Drill_7_6 (a : ℕ → ℝ) (h : a 0 = 1 ∧ a 1 = 2) (h₁: ∀ (n : ℕ), a (n + 2) = a (n + 1) + a n) : a 3 = 5 := by
  have h₂ := h₁ 0
  have h₃ := h₁ 1
  norm_num at h₂ h₃
  linarith
