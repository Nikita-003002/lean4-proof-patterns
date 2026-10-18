-- Q: Let a : ℕ → ℝ be a sequence and n be a natural number. Suppose the sum of the first n terms is 12 and a n = 7. Prove that the sum of the first n + 1 terms is 19.

import Mathlib

theorem Drill_6_2 (n: ℕ) (a : ℕ → ℝ) (h₀: (∑ k ∈ Finset.range n, a k) = 12) (h₁: a n = 7) : (∑ k ∈ Finset.range (n + 1), a k) = 19 := by
  rw [Finset.sum_range_succ]
  linarith
