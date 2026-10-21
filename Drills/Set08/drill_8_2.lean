-- Q: For any real number x, prove that x^2/(x^2 + 1) + 1/(x^2 + 1) = 1.

import Mathlib

theorem Drill_8_2 (x : ℝ) : x^2/(x^2 + 1) + 1/(x^2 + 1) = 1 := by
  field
