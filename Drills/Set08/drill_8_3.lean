-- Q: Let x be a real number such that x ≠ 2 and x ≠ -2. Prove that 1/(x-2) - 1/(x + 2) = 4/(x^2 - 4).

import Mathlib

theorem Drill_8_3 (x : ℝ) (h: x ≠ 2 ∧ x ≠ -2) : 1/(x-2) - 1/(x + 2) = 4/(x^2 - 4) := by
  have h₀: x - 2 ≠ 0 := sub_ne_zero.mpr h.1
  have h₁: x + 2 ≠ 0 := by
    intro h_zero
    apply h.2
    linarith [h.2]
  rw [show x^2 - 4 = (x - 2) * (x + 2) by ring]
  field_simp [h₀, h₁]
  ring
