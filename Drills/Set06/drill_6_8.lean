-- Q: For any natural number n, prove that the sum of first n odd natural numbers equals to n^2.

import Mathlib

theorem Drill_6_8 (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction' n with d hd
  · simp
  · rw [Finset.sum_range_succ, hd]; ring
