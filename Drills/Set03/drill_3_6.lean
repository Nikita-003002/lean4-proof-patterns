-- Q: For any real number x, prove that |2x - 1| + |2x + 1| ≥ 2.

import Mathlib

theorem Drill_3_6 (x : ℝ) : 2 ≤ |2 * x - 1| + |2 * x + 1| := by
  rcases le_total 0 (2 * x - 1) with h | h <;> rcases le_total 0 (2 * x + 1) with h₁ | h₁
  · rw [abs_of_nonneg h, abs_of_nonneg h₁]; linarith
  · rw [abs_of_nonneg h, abs_of_nonpos h₁]; linarith
  · rw [abs_of_nonpos h, abs_of_nonneg h₁]; linarith
  · rw [abs_of_nonpos h, abs_of_nonpos h₁]; linarith
