-- Q: Let x be a real number. Show that |x - 3| + x ≥ 3

import Mathlib

theorem Drill_3_5 (x : ℝ) : 3 ≤ |x - 3| + x := by
  rcases le_total 0 (x - 3) with h | h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_nonpos h]; linarith
