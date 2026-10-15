-- Q: Let n be a natural number. . Suppose that when n is cast to a real number, 19 < n. Prove that 20 ≤ n.

import Mathlib

theorem Drill_4_4 (n : ℕ) (h: 19 < (n : ℝ)): 20 ≤ n := by
  exact_mod_cast h
