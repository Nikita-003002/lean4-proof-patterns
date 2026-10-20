-- Q: Let n be a natural number and x be a real number. Suppose that if n = 0, then x = 0, and we also know x = 19. Prove that n ≠ 0.

import Mathlib

theorem Drill_7_8 (n : ℕ) (x : ℝ) (h₀: n = 0 → x = 0) (h₁: x = 19) : n ≠ 0 := by
  by_contra h
  have hx := h₀ h
  linarith
