-- Q: Prove that there exists an integer x such that 3x + 5 = 26.

import Mathlib

theorem Drill_2_1: ∃ x : ℤ, 3 * x + 5 = 26 := by
  use 7
  norm_num
