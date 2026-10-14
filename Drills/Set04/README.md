# Type Casting and N <-> Z <-> R Bridges

In Lean 4, natural numbers (N), integers (Z), and real numbers (R) are completely separate worlds. Two dangerous "junk value" traps happen in N and Z:
     Truncated Subtraction in N: In N, if `b` is greater than `a`, `a - b = 0` (e.g., `3 - 5 = 0`). Because of this, ring refuses to simplify `(a - b)` in N!
     Truncated Division in N and Z: In N and Z, `5 / 2 = 2`. Whenever an English problem mentions fractions like `n(n+1)/2` or real-number division, cast to R (or Q) or multiply by `2` instead!

<br/>

## Drill 4.1
### `(a b : ℕ) (h₀: b ≤ a) (h₁: a - b = 7): a = b + 7`

- omega converts everything into systems of constraints over integers (Z) rather than natural numbers, adding the condition that variables representing naturals must be ≥.
- The problem is translated into this system of constraints:
    - a ≥ 0 (a : N)
    - b ≥ 0 (b : N)
    - b ≤ a (from `h₀`)
    - a - b = 7 (from `h₁`)
    - Goal to Refute : `a ≠ b + 7`, (To prove `a = b + 7`, omega assumes the opposite and looks for a contradiction).
    - Here subtraction is direct since we have `h₀` i.e. `b ≤ a`
- From `a - b = 7`, we get `a = b + 7`.
- Substitute this into the negated goal: `b + 7 ≠ b + 7`.This simplifies to `0 ≠ 0`, which is fundamentally false.
