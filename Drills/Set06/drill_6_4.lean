-- Q: Let a : ℕ → ℝ be a sequence of real numbers and n be a natural number. Prove that the sum of squares ∑ k = [0, n-1] (a(k))^2 is greater than or equal to 0.

import Mathlib

theorem Drill_6_4_1 (a : ℕ → ℝ) (n : ℕ): 0 ≤ ∑ k ∈ Finset.range (n - 1), (a k)^2 := by
  apply Finset.sum_nonneg
  intro k hk
  exact sq_nonneg (a k)

---

theorem Drill_6_4_2 (a : ℕ → ℝ) (n : ℕ): 0 ≤ ∑ k ∈ Finset.range (n - 1), (a k)^2 := by
  positivity
