-- Q: Let n be a natural number such that (n : R) + 4 < 10. Prove that n ≤ 5.

import Mathlib

theorem Drill_4_5 (n : ℕ) (h: (n : ℝ) + 4 < 10): n ≤ 5 := by
  have h₁: (n : ℝ) < 6 := by linarith
  have h₂: n < 6 := by exact_mod_cast h₁
  omega
