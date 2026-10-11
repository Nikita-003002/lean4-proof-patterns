-- Q: Let x be a real number. Suppose that either x ≤ -2 or x ≥ 5 holds. Prove that if x > 0 then x ≥ 5.

import Mathlib

theorem Drill_3_3 (x : ℝ) (h₀: x ≤ -2 ∨ 5 ≤ x) : 0 < x → 5 ≤ x := by
  intro hx
  rcases h₀ with h | h <;>
  linarith
