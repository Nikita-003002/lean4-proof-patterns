-- Q: Prove that sum of first n natural number is n * (n - 1)/2.

import Mathlib

theorem Drill_6_9 (n : ℕ) : ∑ k ∈ Finset.range n, k = n * (n - 1) / 2 := by
  -- State and prove the division-free version to avoid right/left division headaches
  have H : 2 * ∑ k ∈ Finset.range n, k = n * (n - 1) := by
    induction n with
    | zero => rfl
    | succ k ih =>
      -- Unroll the sum and apply the inductive hypothesis
      rw [Finset.sum_range_succ, mul_add, ih]

      -- Split k to safely handle the natural number subtraction (k - 1)
      obtain rfl | hk := Nat.eq_zero_or_pos k
      · rfl
      -- With k > 0, we can safely push the algebra to integers and let ring solve it
      · zify [hk]; push_cast
        ring

  -- omega effortlessly deduces `Sum = X / 2` from our proof that `2 * Sum = X`
  omega
