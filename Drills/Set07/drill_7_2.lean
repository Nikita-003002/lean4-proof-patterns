-- Q: Let f : ℝ → ℝ be a function satisfying f(x + y) = f(x)+ f(y) for all x and y. Prove that f(0) = 0.

import Mathlib

theorem Drill_7_2_1 (f : ℝ → ℝ) (h: ∀ x y, f (x + y) = f x + f y) : f 0 = 0 := by
  have hk := h 0 0
  simp at hk
  exact hk

---

theorem Drill_7_2_2 (f : ℝ → ℝ) (h: ∀ x y, f (x + y) = f x + f y) : f 0 = 0 := by
  simpa using h 0 0
