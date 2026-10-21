-- Q:  Let a and b be real numbers with b < 0. If a/b ≤ 5, prove that 15b ≤ 3a.

import Mathlib

theorem Drill_8_11 (a b : ℝ) (h₀: b < 0) (h₁: a / b ≤ 5) : 15 * b ≤ 3 * a := by
  rw [div_le_iff_of_neg h₀] at h₁
  linarith
