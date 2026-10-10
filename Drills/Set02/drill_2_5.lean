-- Q: Let a, b and c be integers. If c divided a and b both then pove that it also divides (3a - 5b).

import Mathlib

theorem Drill_2_5 (a b c : ℤ) (h₀: c ∣ a ∧ c ∣ b) : c ∣ (3 * a - 5 * b) := by
  obtain ⟨k, hk⟩ := h₀.left
  obtain ⟨m, hm⟩ := h₀.right
  use 3 * k - 5 * m
  rw[hk, hm]
  ring
