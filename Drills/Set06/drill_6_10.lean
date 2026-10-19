-- Q: For any natural number n, prove the geometric series identity 2 * (∑ k = [0, n-1] 3^k) + 1 = 3^n.

import Mathlib

theorem Drill_6_10 (n : ℕ) : 2 * (∑ k ∈ Finset.range n, 3 ^ k) + 1 = 3 ^ n := by
  induction' n with d hd
  · rfl
  · rw [Finset.sum_range_succ]
    calc
    _ = (2 * (∑ k ∈ Finset.range d, 3^k) + 1) + 2 * 3^d := by ring
    _ = 3^d + 2 * 3^d := by rw [hd]
    _ = 3 ^ (d + 1) := by ring
