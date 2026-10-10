-- Q: Let n be a natural number. If the remainder when n is divided by 6 is 4, Prove that remainder when n is divided by 3 is 1.

import Mathlib

theorem Drill_2_10 (n : ℕ) (h₀ : n % 6 = 4) : n % 3 = 1 := by
  omega
