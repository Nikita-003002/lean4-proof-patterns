-- Q: Let n be a natural number with n ≠ 0 and a : ℕ → ℝ be a sequence such that a(k) < 2 for all k ∈ ℕ. Prove that ∑ k ∈ [0, n-1], a(k) < 2n.

import Mathlib

theorem Drill_6_7 (a : ℕ → ℝ) (n : ℕ) (h₀: n ≠ 0) (h₁ : ∀ k, a k < 2) : ∑ k ∈ Finset.range n, a k < 2 * n := by
  have h: (Finset.range n).Nonempty := by
    apply Finset.nonempty_range_iff.mpr h₀
  have H := Finset.sum_lt_sum_of_nonempty h (fun k _ => h₁ k)
  simp at H
  linarith
