-- Q: Let a : ℕ → ℝ be a sequence such that a₀ = 2, a₁ = 3, and a₂ = 5. Prove that sum of aκ over k = [0, 2] is 10.

import Mathlib

theorem Drill_6_3 (a : ℕ → ℝ) (h: a 0 = 2 ∧ a 1 = 3 ∧ a 2 = 5) : ∑ k ∈ Finset.range 3, a k = 10 := by
  simp [Finset.sum_range_succ, h]
  norm_num
