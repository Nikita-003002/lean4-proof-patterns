-- Q: Let a and b be natural numbers such that b ≤ a. Prove that (a - b)^2 = a^2 + b^2 - 2ab.

import Mathlib

theorem Drill_4_2 (a b : ℕ) (h₀: b ≤ a) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by
    have h₁: 2 * a * b ≤ a ^ 2 + b ^ 2 := by
        zify
        nlinarith
    zify [h₀, h₁]
    ring
