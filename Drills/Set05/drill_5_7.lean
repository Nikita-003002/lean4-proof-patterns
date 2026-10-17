-- Q: Let x, y ∈ ℝ such that x + y = 3 and xy = 1. Prove x^4 + y^4 = 47.

import Mathlib

theorem drill_5_7_2 (x y : ℝ) (h₁ : x + y = 3) (h₂ : x * y = 1) : x^4 + y^4 = 47 := by
  have h: x ^ 4 + y ^ 4 = ((x + y) ^ 2 - 2 * (x * y)) ^ 2 - 2 * (x * y) ^ 2 := by ring
  rw [h, h₁, h₂]
  norm_num

---

theorem drill_5_7_1 (x y : ℝ) (h₁ : x + y = 3) (h₂ : x * y = 1) : x^4 + y^4 = 47 := by
  calc
  _ = (x ^ 2 + y ^ 2) ^ 2 - 2 * (x * y) ^ 2 := by ring
  _ = ((x + y) ^ 2 - 2 * (x * y)) ^ 2 - 2 * (x * y) ^ 2 := by ring
  _ = 47 := by rw [h₁, h₂]; norm_num
