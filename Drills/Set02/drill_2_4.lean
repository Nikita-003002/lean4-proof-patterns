-- Q: For any integer n, if 5 divided n, Prove that 5 divides n^2 + 10n.

import Mathlib

theorem Drill_2_4 (n : ℤ) (h₀: 5 ∣ n) : 5 ∣ (n ^ 2 + 10 * n) := by
  obtain ⟨k, hk⟩ := h₀
  use 5 * k ^ 2 + 10 * k
  rw[hk]
  ring
