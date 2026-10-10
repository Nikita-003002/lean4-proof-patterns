-- Q: For any integer n, Prove that 3 divides the sum of three consecutive integer n, (n + 1), (n + 2).

import Mathlib

theorem Drill_2_7 (n : ℤ) : 3 ∣ (n + (n + 1) + (n + 2)) := by
  use n + 1
  ring
