-- Q: For all real numbers a and b, prove that max(a, b) + min(a, b) = a + b.

import Mathlib

theorem Drill_3_7 (a b : ℝ): max a b + min a b = a + b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h]; ring
  · rw [max_eq_left h, min_eq_right h]
