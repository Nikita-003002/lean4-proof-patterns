-- Q: Let a and b be natural number such that b ≤ a and a - b = 7. Prove that a = b + 7.

import Mathlib

theorem Drill_4_1 (a b : ℕ) (h₀: b ≤ a) (h₁: a - b = 7): a = b + 7 := by
  omega
