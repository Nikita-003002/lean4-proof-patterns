-- Q: Let n be a natural number. Suppose we define the sum of the first n integers via the real-number equation 2S = ((n * (n + 1) : N) : R). Prove that S = (n : R)((n : R) + 1)/2

import Mathlib

theorem Drill_4_8 (n S: ℕ) (h: 2 * S = ((n * (n + 1) : ℕ) : ℝ)) : S = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  push_cast at h
  linarith
