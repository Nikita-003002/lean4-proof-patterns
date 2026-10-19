-- Q: Let n be a natural number. Prove that sum of constant real number 5 over k ∈ [1, 5] is 5n.

import Mathlib

theorem Drill_6_1 (n : ℕ): ∑ _ ∈ Finset.range n, (5 : ℝ) = 5 * n := by
  simp
  ring
