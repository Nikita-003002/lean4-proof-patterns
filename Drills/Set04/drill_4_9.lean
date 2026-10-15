-- Q: Let n be a natural number such that 2n + 1 < 15 in N. Prove that (n : R) < 7 in R.

import Mathlib

theorem Drill_4_9 (n : ℕ) (h: 2 * n + 1 < 15): (n : ℝ) < 7 := by
  have h₀: n < 7 := by omega
  exact_mod_cast h₀
