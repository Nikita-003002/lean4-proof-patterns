-- Q: Let R be any commutative ring, and let x, y in R. If x + y = 7 and xy = 10, prove that x^2 + y^2 = 29.

import Mathlib

theorem drill_5_1_1 {R : Type*} [CommRing R] (x y : R) (h₁ : x + y = 7) (h₂ : x * y = 10) :
    x^2 + y^2 = 29 := by
  linear_combination (x + y + 7) * h₁ - 2 * h₂

---

theorem drill_5_1_2 {R : Type*} [CommRing R] (x y : R) (h₁ : x + y = 7) (h₂ : x * y = 10) :
    x^2 + y^2 = 29 := by
  rw [show x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) by ring]
  rw [h₁, h₂]
  norm_num

---

theorem drill_5_1_3 {R : Type*} [CommRing R] (x y : R) (h₁ : x + y = 7) (h₂ : x * y = 10) :
    x^2 + y^2 = 29 := by
  calc
  _ = (x + y) ^ 2 - 2 * (x * y) := by ring
  _ = 29 := by rw [h₁, h₂]; norm_num
