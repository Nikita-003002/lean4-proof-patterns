-- Q: Let f : ℝ → ℝ be a function. Suppose it is false that every real number has an output ≤ 0. Prove that there exists a real number x such that f(x) + 1 > 1.

import Mathlib

theorem Drill_7_10 (f : ℝ → ℝ) ( h : ¬ (∀ x : ℝ, f x ≤ 0)) : ∃ (x : ℝ), 1 < f x + 1 := by
  push Not at h
  obtain ⟨k, hk⟩ := h
  use k
  linarith
