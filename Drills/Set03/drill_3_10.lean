-- Q: For any integer n, prove that 2 divides n + n^2.

import Mathlib

theorem Drill_3_10 (n : ℤ) : 2 ∣ (n + n ^ 2) := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · use 2 * k ^ 2 + k; rw [hk]; ring
  · use (2 * k + 1) * (k + 1); rw [hk]; ring
