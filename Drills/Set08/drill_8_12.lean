-- Q: Let a, b, and c be real numbers with b < 0. If a/b < c, prove that cb < a.

import Mathlib

theorem Drill_8_12 (a b c : ℝ) (h₀: b < 0) (h₁: a / b < c) : c * b < a := by
  rw [div_lt_iff_of_neg h₀] at h₁
  exact h₁
