-- Q: Let a and b be real numbers with b > 0. Suppose a/b ≤ 3. Prove that a ≤ 3b.

import Mathlib

theorem Drill_8_5 (a b : ℝ) (h₀ : 0 < b) (h₁: a / b ≤ 3) : a ≤ 3 * b := by
  field_simp at h₁
  linarith
