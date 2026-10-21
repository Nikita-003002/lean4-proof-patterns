-- Q: Let x, y, and z be real numbers with y > 0. Prove the logical equivalence (x/y ≤ z) ↔ (x ≤ zy)

import Mathlib

theorem Drill_8_13 (x y z : ℝ) (h : 0 < y) : (x / y ≤ z) ↔ (x ≤ z * y) := by
  exact div_le_iff₀ h
