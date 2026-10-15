-- Q: Let n be a natural number such that n ≥ 3. Prove that natural identity that (n + 3)(n - 3) + 9 = n^2

import Mathlib

theorem Drill_4_3 (n : ℕ) (h: n ≥ 3): (n + 3) * (n - 3) + 9 = n ^ 2 := by
  zify [h]
  ring
