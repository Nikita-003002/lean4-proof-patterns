-- Q: Let a, b and c be real numbers such that it satisfy c = 10 + |a - 1| + |b - 2|. Show that 10 ≤ c.

import Mathlib

theorem Drill_1_6 (a b c : ℝ) (h₀: c = 10 + |a - 1| + |b - 2|) : 10 ≤ c := by
  linarith [abs_nonneg (a - 1), abs_nonneg (b - 2)]
