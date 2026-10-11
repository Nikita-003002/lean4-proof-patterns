-- Q: Let x be a real number such that |x - 4| ≤ 3. Prove that 1 ≤ x and x ≤ 7.

import Mathlib

theorem Drill_3_1 (x : ℝ) (h₀: |x - 4| ≤ 3) : 1 ≤ x ∧ x ≤ 7 := by
  rw [abs_le] at h₀
  constructor <;> linarith
