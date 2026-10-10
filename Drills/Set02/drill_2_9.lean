-- Q: Let a and b be integers such that a is even and b is odd. Prove that sum of a and b is odd.

import Mathlib

theorem Drill_2_9 (a b  : ℤ) (h₀ : Even a) (h₁ : Odd b) : Odd (a + b) := by
  obtain ⟨k, hk⟩ := h₀
  obtain ⟨m, hm⟩ := h₁
  use k + m
  rw [hk, hm]
  ring
