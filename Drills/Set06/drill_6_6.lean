-- Q: Let a : ℕ → ℝ be a sequence such that a(k) ≤ 3 for all k ∈ ℕ. Prove that for any natural number n, ∑ k ∈ [0, n-1] a(k) ≤ 3n.

import Mathlib

theorem Drill_6_6 (a : ℕ → ℝ) (n : ℕ) (h: ∀ k, a k ≤ 3): ∑ k ∈ Finset.range n, a k ≤ 3 * n := by
  have h₀: ∑ k ∈ Finset.range n, a k ≤ ∑ k ∈ Finset.range n, 3 := by
    apply Finset.sum_le_sum
    intro k hk
    exact h k
  simp at h₀
  linarith
