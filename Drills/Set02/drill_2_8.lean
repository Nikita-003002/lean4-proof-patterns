-- Q: Let n be an integer. If n is odd, prove that n^2 - 1 is divisible by 4.

import Mathlib

theorem Drill_2_8 (n : ℤ) (h₀ : Odd n) : 4 ∣ (n ^ 2 - 1) := by
  obtain ⟨k, hk⟩ := h₀
  use k ^ 2 + k
  rw[hk]
  ring
