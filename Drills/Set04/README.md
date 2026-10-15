# Type Casting and N <-> Z <-> R Bridges

- In Lean 4, natural numbers (N), integers (Z), and real numbers (R) are completely separate worlds. Two dangerous "junk value" traps happen in N and Z:
    - Truncated Subtraction in N: In N, if `b` is greater than `a`, `a - b = 0` (e.g., `3 - 5 = 0`). Because of this, ring refuses to simplify `(a - b)` in N!
    - Truncated Division in N and Z: In N and Z, `5 / 2 = 2`. Whenever an English problem mentions fractions like `n(n+1)/2` or real-number division, cast to R (or Q) or multiply by `2` instead!

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

<br/>

## Drill 4.2
### `(a b : ℕ) (h₀: b ≤ a) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b`

- zify scans the goal for natural number subtraction (-) and demands proofs that the left operand is greater than or equal to the right operand to prevent truncation to zero.

- Subtraction 1: `(a - b)` is cleared by the provided hypothesis `h₀` : `b ≤ a`.

- Subtraction 2: `((a ^ 2 + b ^ 2) - 2 * a * b) `lacks a hypothesis proving `2 * a * b ≤ a ^ 2 + b ^ 2`.

- Because of this missing proof, zify refuses to unpack the right side, leaving it trapped behind a cast barrier: `↑(a ^ 2 + b ^ 2 - 2 * a * b)`.

- have `h₁` : `2 * a * b ≤ a ^ 2 + b ^ 2` is explicitly declared as a sub-goal to force the cast.

    - Inside the sub-goal, `zify` pushes the isolated inequality into `ℤ`.

    - `nlinarith` acts as a preprocessor for `linarith` providing obvious info like `0 ≤ (a - b)^2`:
        - Let the non-linear terms be substituted as `X = ab`, `Y = a^2`, and `Z = b^2`.
        - Original Goal: `2X ≤ Y + Z`
        - Negated Goal: `2X > Y + Z` for `linarith`.
        - nlinarith Fact: `0 ≤ Y - 2X + Z` i.e. `0 ≤ (a - b)^2` {Since square}
        - Move all terms to the left to get standard `(< 0)` format: 
            - `Goal_Neg`:` Y + Z - 2X < 0`
            - `nlinarith_Fact`: `- Y + 2X - Z ≤ 0`
        - Clearly a contradiction of `0 < 0` arises after addition of `Goal_Neg` and `nlinarith_Fact`. Closing the goal.

- With `h₁` successfully proven, `zify [h₀, h₁]` is fed the bounds for both subtractions and successfully unpacks the entire main goal into pure ℤ: `(↑a - ↑b) ^ 2 = ↑a ^ 2 + ↑b ^ 2 - 2 * ↑a * ↑b`.

- `ring` normalizes the expanded terms on both sides of the pure `ℤ` equation and closes the proof.

>[!Note]
> In `ℤ`, `(a - b)^2 ≤ 0` is guaranteed without truncation traps.

<br/>

## Drill 4.3
### `(n : ℕ) (h: n ≥ 3): (n + 3) * (n - 3) + 9 = n ^ 2`

- `ring` requires a valid commutative ring, but natural numbers (`ℕ`) fail this because subtraction truncates at zero (e.g., `2 - 3 = 0`).
- `zify` scans the goal for the natural number subtraction `(n - 3)` and demands a proof that `3 ≤ n` to safely cast it into integers (`ℤ`).
- Subtraction 1: `(n - 3)` is immediately cleared by feeding `zify` the provided hypothesis `h` : `n ≥ 3` (which is definitionally `3 ≤ n`).
- With the bound satisfied, `zify [h]` unpacks the equation out of `ℕ` and casts it entirely into pure `ℤ`: `(↑n + 3) * (↑n - 3) + 9 = ↑n ^ 2`.
- Since `ℤ` is a true commutative ring, `ring` can now algebraically expand the left side to `↑n^2 - 9 + 9`, normalize both sides to exactly `↑n^2`, and close the goal.


<br/>

## Drill 4.4
### `(n : ℕ) (h: 19 < (n : ℝ)): 20 ≤ n`

- Lean implicitly expands `19 < (n : ℝ)` to match types across the operator: `(↑19 : ℝ) < (↑n : ℝ)`.
- `exact_mod_cast` fetches the `@[norm_cast]` lemma `Nat.cast_lt`, which states `(↑a : ℝ) < (↑b : ℝ) ↔ a < b`.
- It applies this lemma to strip the real-number casts, pulling the hypothesis down into pure `ℕ`: `19 < n`.
- On `ℕ`, strict inequality `a < b` is definitionally `a + 1 ≤ b`. Lean automatically evaluates `19 < n` as `20 ≤ n`.
- The transformed hypothesis now exactly matches the target goal `20 ≤ n`, closing the proof.

<br/>

## Drill 4.5
### `(n : ℕ) (h: (n : ℝ) + 4 < 10): n ≤ 5`

- `linarith` performs real-number arithmetic on `h`, subtracting 4 from both sides to establish `h₁`: `(n : ℝ) < 6`.
- `exact_mod_cast` strips the real-number coercions from `h₁`, pulling the inequality down into pure `ℕ` as `h₂`: `n < 6`.
- `omega` evaluates this new pure `ℕ` hypothesis. Recognizing that strictly less than 6 (`n < 6`) is mathematically identical to less than or equal to 5 (`n ≤ 5`) in the discrete domain of natural numbers, it perfectly matches the goal and closes the proof.

<br/>

## Drill 4.6
### `(a b : ℕ) (h₀: (a : ℝ) + (b : ℝ) = 12) (h₁: (a : ℝ) - (b : ℝ) = 4) : a = 8`

- `linarith` handles linear systems over the reals (`ℝ`). It automatically combines `h₀` and `h₁` (adding them to get `2a = 16`) to deduce the intermediate step `h`: `(a : ℝ) = 8`.
- `h` is mathematically correct but type-mismatched. Internally, Lean represents it with type casts: `(↑a : ℝ) = (↑8 : ℝ)`.
- `exact_mod_cast` fetches the `@[norm_cast]` equality lemma (`Nat.cast_inj`), which establishes that `(↑x : ℝ) = (↑y : ℝ) ↔ x = y`.
- It applies this lemma to strip the real-number coercions entirely, pulling the equation down into pure `ℕ` as `a = 8`.
- The type-corrected hypothesis now exactly matches the final target goal `a = 8`, closing the proof.

<br/>

## Drill 4.7
### `(n : ℕ) : (((n + 1) ^ 2 : ℕ) : ℝ) = (n : ℝ)^ 2 + 2 * (n : ℝ) + 1`

- The initial goal has a real-number cast wrapping the entire left-side expression: `↑((n + 1) ^ 2)`.
- `push_cast` systematically pushes these coercions inward by distributing the cast across the power and addition. It rewrites the left side into `(↑n + 1) ^ 2`, placing the operations entirely in `ℝ`.
- With the equation now safely situated in the commutative ring of real numbers (`ℝ`), the `ring` tactic takes over.
- `ring` algebraically expands the new left side `(↑n + 1) ^ 2` into `↑n ^ 2 + 2 * ↑n + 1`, making it perfectly match the right side and closing the proof.

<br/>

## Drill 4.8
### `(n S: ℕ) (h: 2 * S = ((n * (n + 1) : ℕ) : ℝ)) : S = (n : ℝ) * ((n : ℝ) + 1) / 2`

- `push_cast at h` scans hypothesis `h` and targets the right side, which is trapped behind a single outward cast barrier: `↑(n * (n + 1))`.
- It forces the coercion inward, distributing it across both the multiplication and the addition to unpack the equation entirely into `ℝ` as `2 * ↑S = ↑n * (↑n + 1)`.
- linarith acts on the updated hypothesis and the goal. Since it only understands linear relationships, it treats the non-linear chunk as an opaque, independent variable.
- Let the non-linear term be substituted as `X` = `↑n * (↑n + 1)`.
    - Original Goal: `↑S = X / 2`
    - Hypothesis `h`: `2 * ↑S = X`
    - Because it relies on inequalities, it splits this negated goal into two separate contradiction tracks: `Case 1` : `(↑S < X / 2)` and `Case 2` : `(↑S > X / 2)`.
    - `Case 1`:
        - Sub-goal: `↑S < X / 2`
        - Multiply by the scalar 2 to clear fractions: `2 * ↑S < X`.
        - Move terms to standard (< 0) format: `Goal_Neg` :` 2 * ↑S - X < 0`.
        - Format hypothesis h for addition: `h_Fact` : `-2 * ↑S + X = 0`.
        - linarith adds `Goal_Neg` and `h_Fact`. The variables perfectly cancel, yielding `0 < 0`. Contradiction found.
    - `Case 2`:
        - Sub-goal: `↑S > X / 2` (which means `X / 2 < ↑S`).
        - Multiply by 2 and move to standard format: `Goal_Neg` :` X - 2 * ↑S < 0`.
        - Format hypothesis h for addition: `h_Fact` : `2 * ↑S - X = 0`.
        - linarith adds `Goal_Neg` and `h_Fact`. The variables cancel again, yielding `0 < 0`. Contradiction found.
        - With both branches of the negated goal fatally crashing into `0 < 0`, linarith proves the original equality must be true and closes the main goal.

<br/>

## Drill 4.9
### `(n : ℕ) (h: 2 * n + 1 < 15): (n : ℝ) < 7`

- `omega` is invoked to solve the intermediate sub-goal `h₀`: `n < 7`. Operating in pure `ℕ`, it uses Presburger arithmetic to negate the target and hunt for a contradiction.
- Negated Sub-goal: `n ≥ 7`.
- `omega` multiplies by 2 and adds 1, logically deducing that if `n ≥ 7`, then `2 * n + 1 ≥ 15`.
- This fatally crashes into the provided hypothesis `h`: `2 * n + 1 < 15`. The contradiction proves the sub-goal, successfully generating `h₀`: `n < 7`.
- The main goal is trapped behind real-number casts. Internally, Lean sees `(↑n : ℝ) < (↑7 : ℝ)`.
- `exact_mod_cast` fetches the `@[norm_cast]` equivalence lemma `Nat.cast_lt`, which states `(↑a : ℝ) < (↑b : ℝ) ↔ a < b`.
- It applies this lemma to strip the coercions out of the target goal, pulling it down into the natural number domain as exactly `n < 7`.
- The type-corrected goal now perfectly matches the established `h₀`, closing the proof.

<br/>

## Drill 4.10
### `(n : ℕ) (h: (n : ℝ) ^ 2 < 30): n ≤ 5 `
- `by_contra! h_contra` negates the target goal `n ≤ 5` to hunt for a contradiction, generating the strict inequality `h_contra`: `5 < n`.
- Because `5 < n` is definitionally evaluated as `6 ≤ n` in the discrete domain of `ℕ`, `exact_mod_cast` implicitly leverages this tighter bound when bridging domains. It applies structural lemmas to push the hypothesis up into `ℝ`, adding the necessary real-number coercions to establish `h₀`: `6 ≤ ↑n`.
- The active goal is now `False`. `nlinarith` takes over to find the mathematical crash between `h` and `h₀`.
- Seeing `h₀` (`6 ≤ ↑n`), `nlinarith` acts as a non-linear preprocessor and automatically generates the squared bounding fact: `nlinarith_Fact`: `36 ≤ ↑n^2`.
- Let the non-linear term be substituted as `Y = ↑n^2`.
- Format hypothesis `h` for addition: `Y - 30 < 0`.
- Format `nlinarith_Fact` for addition: `36 - Y ≤ 0`.
- `nlinarith` adds both equations. The `Y` variables perfectly cancel out, yielding `6 < 0`. This fatal contradiction proves the original goal must be true, closing the proof.