-- Q: Let a : ℕ → ℝ be a sequence such that a_{n+1} = -a_n for all n ∈ ℕ. Prove that for all n ∈ ℕ, a_{n+2} = a_n.

import Mathlib

theorem Drill_7_7 (a : ℕ → ℝ) (h: ∀ (n : ℕ), a (n + 1) = - a n) : ∀ n, a (n + 2) = a n := by
  intro n
  have h₀ := h n
  have h₁ := h (n + 1)
  linarith
