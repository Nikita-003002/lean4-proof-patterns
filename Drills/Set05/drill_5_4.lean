-- Q: Let R be any commutative ring, and x, y, z ∈ R. Suppose x + y + z = 0. Prove x^3 + y^3 + z^3 = 3xyz..

import Mathlib

theorem Drill_5_4_1 {R : Type*} [CommRing R] (x y z : ℝ) (h: x + y + z = 0) : x ^ 3 + y ^ 3 + z ^ 3 = 3 * x * y * z := by
  linear_combination (x^2 + y^2 + z^2 - x*y - y*z - z*x) * h

---

theorem Drill_5_4_2 {R : Type*} [CommRing R] (x y z : ℝ) (h: x + y + z = 0) : x ^ 3 + y ^ 3 + z ^ 3 = 3 * x * y * z := by
  have hk: z = - x - y := by linarith
  rw [hk]
  ring
