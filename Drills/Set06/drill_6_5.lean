-- Q: Let a, b : ℕ → ℝ be two sequences of real numbers such that a(k) ≤ b(k) for all k ∈ ℕ. Prove that for any natural number n, ∑ k ∈ [0, n-1] a(k) ≤ b(k).

import Mathlib

theorem Drill_6_5 (a b : ℕ → ℝ) (n : ℕ) (h: ∀ k, a k ≤ b k) : ∑ k ∈ Finset.range n, a k ≤ ∑ k ∈ Finset.range n, b k := by
  apply Finset.sum_le_sum
  intro k hk
  exact h k
