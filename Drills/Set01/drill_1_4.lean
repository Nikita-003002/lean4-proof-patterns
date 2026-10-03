-- Q: For any three real numbers a, b and c, show that ab + bc + ca ≤ a^2 + b^2 + c^2.

import Mathlib

theorem Drill_1_4 (a b c : ℝ) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
 