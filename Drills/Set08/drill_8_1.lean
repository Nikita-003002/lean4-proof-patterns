-- Q: Let a and b be non-zero real numbers. Prove that 1/a + 1/b = (a + b)/ab.

import Mathlib

theorem Drill_8_1 (a b : ℝ) (h : a ≠ 0 ∧ b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) := by
  field_simp [h]
  ring
