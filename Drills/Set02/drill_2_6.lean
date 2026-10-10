-- Q: Let a, b and c be integers. Prove that if a divides b and b divides c then a divides c.

import Mathlib

theorem Drill_2_6 (a b c : ℤ) (h₀: a ∣ b) (h₁: b ∣ c) : a ∣ c := by
  obtain ⟨k, hk⟩ := h₀
  obtain ⟨m, hm⟩ := h₁
  use k * m
  rw [hm, hk]
  ring
