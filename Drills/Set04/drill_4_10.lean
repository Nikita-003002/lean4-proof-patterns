-- Q:  Let n be a natural number such that (n : R)^2 < 30. Prove that n ≤ 5.

import Mathlib

theorem Drill_4_10 (n : ℕ) (h: (n : ℝ) ^ 2 < 30): n ≤ 5 := by
  by_contra! h_contra
  have h₀: 6 ≤ (n : ℝ) := by exact_mod_cast h_contra
  nlinarith
