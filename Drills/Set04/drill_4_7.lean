-- Q: Let n be a natural number. Prove that when the natural number expression (n + 1)^2 is cast to R, it equals (n : R)^2 + 2(n : R) + 1.

import Mathlib

theorem Drill_4_7 (n : ℕ) : (((n + 1) ^ 2 : ℕ) : ℝ) = (n : ℝ)^ 2 + 2 * (n : ℝ) + 1 := by
  push_cast
  ring
