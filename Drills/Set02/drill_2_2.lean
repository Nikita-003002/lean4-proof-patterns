-- Q: Let a and b be integers. Suppose that there exists an integer k such that a = 4k + 1.
--, and there exists an integer m such that b = 4m + 3. Prove that there exists an integer n such that a + b = 4n.

import Mathlib

theorem Drill_2_2 (a b : ℤ) (h₀: ∃ k : ℤ, a = 4 * k + 1) (h₁: ∃ m : ℤ, b = 4 * m + 3) : ∃ n : ℤ, a + b = 4 * n := by
  obtain ⟨k, hk⟩ := h₀
  obtain ⟨m, hm⟩ := h₁
  use k + m + 1
  rw [hk, hm]
  ring
