-- Q: Let a and b be real numbers. Show that max(a, b) - min(a, b) = |a - b|.

import Mathlib

theorem Drill_3_8 (a b : ℝ) : max a b - min a b = |a - b| := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (show a - b ≤ 0 by linarith)]; ring
  · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (show 0 ≤ a - b by linarith)]
