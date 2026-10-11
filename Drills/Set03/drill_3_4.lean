-- Q: For any real number x, prove that x ≤ |x|.

import Mathlib

theorem Drill_3_4 (x : ℝ) : x ≤ |x| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]
    linarith
