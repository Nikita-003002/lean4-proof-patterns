-- Q: Let x be an integer. Suppose there exists an integer k such that x = 3k + 2.
-- Prove that there exists an integer m such that x^2 = 3m + 1.

import Mathlib

theorem Drill_2_3 (x : ℤ) (h₀: ∃ k, x = 3 * k + 2) : ∃ m, x ^ 2 = 3 * m + 1 := by
  obtain ⟨k, hk⟩ := h₀
  use 3 * k ^ 2 + 4 * k + 1
  rw[hk]
  ring
