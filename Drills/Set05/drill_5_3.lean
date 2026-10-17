-- Q: Let x and y be real numbers such that x + y = 4 and xy = 2. Prove that x^3 + y^3 = 40.

import Mathlib

theorem Drill_5_3_1 (x y : ℝ) (h₀: x + y = 4) (h₁: x * y = 2): x ^ 3 + y ^ 3 = 40 := by
  calc
    _ = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by ring
    _ = 40 := by rw [h₀, h₁]; norm_num

---
theorem Drill_5_3_2 (x y : ℝ) (h₀: x + y = 4) (h₁: x * y = 2): x ^ 3 + y ^ 3 = 40 := by
  rw [show x^3 + y^3 = (x + y)^3 - 3 * (x * y) * (x + y) by ring]
  rw [h₀, h₁]
  norm_num

---
theorem Drill_5_3_3 (x y : ℝ) (h₀: x + y = 4) (h₁: x * y = 2): x ^ 3 + y ^ 3 = 40 := by
  linear_combination ((x + y)^2 + 4 * (x + y) + 10) * h₀ - 3 * (x + y) * h₁
