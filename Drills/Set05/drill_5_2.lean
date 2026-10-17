-- Q: Suppose z and w are complex numbers satisfying z - w = 3 and zw = 4. Show that (z + w)^2 = 25.

import Mathlib

theorem drill_5_2_1 (z w : ℂ) (h₀ : z - w = 3) (h₁ : z * w = 4) : (z + w)^2 = 25 := by
  linear_combination (z - w + 3) * h₀ + 4 * h₁

---
theorem drill_5_2_2 (z w : ℂ) (h₀ : z - w = 3) (h₁ : z * w = 4) : (z + w)^2 = 25 := by
  rw [show (z + w) ^ 2 = (z - w) ^ 2 + 4 * (z * w) by ring]
  rw [h₀, h₁]
  ring

---
theorem drill_5_2_3 (z w : ℂ) (h₀ : z - w = 3) (h₁ : z * w = 4) : (z + w)^2 = 25 := by
  calc
  _ = (z - w) ^ 2 + 4 * (z * w) := by ring
  _ = 25 := by rw [h₀, h₁]; ring
