# Quantifiers (∀), Functions & Contradiction

- When a hypothesis states a rule applies to all values (`∀ x`), the solver cannot guess which ones matter. We must explicitly generate the equations needed by plugging in concrete values like `0`, `1`, `x`, or `-x` (e.g., `have h₀ := h 0`).
- `linarith` treats function applications as opaque symbols. It does not know that `f (1 - 0)` is the same variable as `f 1`. Always use `norm_num` or `simp` to evaluate internal arithmetic so the variables match perfectly before the final step.
- Because `linarith` works by negating your target goal to find a contradiction, the goal itself must be a clean equality or inequality. Unpack complex logic first: use `intro` to pull variables and implications into the local context, `by_contra` for `≠` goals, and `push Not` to unwrap negated universal statements.

<br/>

## Drill 7.1
### `(f : ℝ → ℝ) (h₀: ∀ x, f (x + 1) = f x + 3) (h₁: f 0 = 5) : f 2 = 11`

- `have _ := h₀ 0` and `have _ := h₀ 1` apply the universal rule `h₀` to the specific inputs `0` and `1`. This automatically generates the intermediate equations `f (0 + 1) = f 0 + 3` and `f (1 + 1) = f 1 + 3` without assigning them specific variable names.
- `norm_num at *` evaluates the simple addition inside the function arguments across all active hypotheses. This simplifies `0 + 1` to `1` and `1 + 1` to `2`, so Lean can recognize `f 1` and `f 2` as matching variables.
- `linarith` substitutes `f 0 = 5` into the first equation to find `f 1 = 8`, and substitutes that into the second equation to prove `f 2 = 11`, closing the goal.

<br/>

## Drill 7.2 (Two Approaches)
### `(f : ℝ → ℝ) (h: ∀ x y, f (x + y) = f x + f y) : f 0 = 0`

- Approach 1:
    - `have hk := h 0 0` applies the universal rule `h` specifically to `x = 0` and `y = 0`, generating the hypothesis `hk : f (0 + 0) = f 0 + f 0`.
    - `simp at hk` automatically evaluates `0 + 0` to `0`, turning the equation into `f 0 = f 0 + f 0`. It then simplifies the algebra by subtracting `f 0` from both sides, leaving `hk : 0 = f 0` (or `f 0 = 0`).
    - `exact hk` closes the goal since `hk` now perfectly matches the theorem's target.


- Approach 2: `simpa`
    - `simpa using h 0 0` compresses the entire first approach into a single line. It takes the unsimplified expression `f (0 + 0) = f 0 + f 0`, runs the `simp` simplifier on it (which reduces it to `f 0 = 0`), and immediately applies it to close the matching goal.

<br/>

## Drill 7.3
### `(f : ℝ → ℝ) (h: ∀ x y : ℝ, f (x + y) = f x + f y) : ∀ x, f (-x) = - f x`

- `intro x` brings an arbitrary real number `x` into the local context to satisfy the universal quantifier `∀ x` in the goal.
- `have h₀ := h (-x) (x)` and `have h₁ := h 0 0` apply the additivity rule to specific inputs, generating the intermediate equations `f (-x + x) = f (-x) + f x` and `f (0 + 0) = f 0 + f 0`.
- `simp at h₀ h₁` evaluates the basic arithmetic and simplifies the algebra. It reduces `-x + x` to `0` in `h₀` (yielding `f 0 = f (-x) + f x`), and simplifies `h₁` down to the fundamental baseline `f 0 = 0`.
- `linarith` targets the goal `f (-x) = - f x` and works by refutation. It negates the goal (assuming `f (-x) ≠ - f x`) and combines it with the simplified linear equations `h₀` and `h₁`. This combination yields a mathematical contradiction, proving the original goal must be true and closing the proof.

</br>

## Drill 7.4
### `(f : ℝ → ℝ) (h: ∀ x, 2 * f x + f (1-x) = 3 * x) : f 1 = 2`

- `have h₀ := h 0` and `have h₁ := h 1` apply the universal rule `h` to the specific inputs `0` and `1`, generating two intermediate equations: `2 * f 0 + f (1 - 0) = 3 * 0` and `2 * f 1 + f (1 - 1) = 3 * 1`.
- `norm_num at h₀ h₁` evaluates the basic arithmetic inside the function arguments and on the right sides. It simplifies `1 - 0` to `1` and `1 - 1` to `0`, transforming the hypotheses into a clean linear system: `2 * f 0 + f 1 = 0` and `2 * f 1 + f 0 = 3`.
- `linarith` targets the main goal `f 1 = 2` and works by refutation. It negates the goal (assuming `f 1 ≠ 2`) and systematically combines it with the simplified linear equations `h₀` and `h₁`. This combination yields a mathematical contradiction (such as `0 < 0` or `False`), proving the original goal must be true and closing the proof.

</br>

## Drill 7.5
### `(f : ℝ → ℝ) (h : ∀ x, 2 * f x + f (-x) = 3 * x) : ∀ x, f x = 3 * x`

- `intro x` brings an arbitrary real number `x` into the local context to satisfy the universal quantifier `∀ x` in the goal.
- `have h₀ := h (x)` and `have h₁ := h (-x)` apply the universal rule `h` to the specific inputs `x` and `-x`, generating two intermediate equations: `2 * f x + f (-x) = 3 * x` and `2 * f (-x) + f (- -x) = 3 * -x`.
- `norm_num at h₁` evaluates the basic arithmetic and simplifies the algebra. It reduces the double negative `- -x` to `x` and cleanly formats the right side, transforming `h₁` into the clean linear equation `2 * f (-x) + f x = -3 * x`.
- `linarith` targets the main goal `f x = 3 * x` and works by refutation. It negates the goal (assuming `f x ≠ 3 * x`) and combines it with the simplified linear equations `h₀` and `h₁`. This combination yields a mathematical contradiction, proving the original goal must be true and closing the proof.

<br/>

## Drill 7.6
### `(a : ℕ → ℝ) (h : a 0 = 1 ∧ a 1 = 2) (h₁: ∀ (n : ℕ), a (n + 2) = a (n + 1) + a n) : a 3 = 5`

- `have h₂ := h₁ 0` and `have h₃ := h₁ 1` apply the universal recursive rule `h₁` to the specific inputs `0` and `1`, generating two intermediate equations: `a (0 + 2) = a (0 + 1) + a 0` and `a (1 + 2) = a (1 + 1) + a 1`.
- `norm_num at h₂ h₃` evaluates the basic arithmetic inside the sequence indices. It simplifies the addition to transform the hypotheses into properly indexed terms: `a 2 = a 1 + a 0` and `a 3 = a 2 + a 1`.
- `linarith` targets the main goal `a 3 = 5` and works by refutation. It negates the goal (assuming `a 3 ≠ 5`) and combines it with the base cases in `h` (`a 0 = 1`, `a 1 = 2`) and the simplified linear equations `h₂` and `h₃`. This combination yields a mathematical contradiction, proving the original goal must be true and closing the proof.

</br>

## Drill 7.7
### `(a : ℕ → ℝ) (h: ∀ (n : ℕ), a (n + 1) = - a n) : ∀ n, a (n + 2) = a n`

- The theorem asks to prove that if a sequence negates its value at each step, its values repeat every two steps (i.e., a_{n+2} = a_n).
- `intro n` brings an arbitrary natural number `n` into the local context to satisfy the universal quantifier `∀ n` in the goal.
- `have h₀ := h n` and `have h₁ := h (n + 1)` apply the alternating rule `h` to the specific sequence indices `n` and `n + 1`. This generates two intermediate equations: `a (n + 1) = -a n` and `a (n + 1 + 1) = -a (n + 1)`.
- *(Note: Lean definitionally recognizes `n + 1 + 1` as identical to the `n + 2` in the goal, so no `norm_num` is needed here).*
- `linarith` targets the main goal `a (n + 2) = a n` and works by refutation. It negates the goal (assuming `a (n + 2) ≠ a n`) and combines it with the linear equations `h₀` and `h₁`. This combination yields a mathematical contradiction, proving the original goal must be true and closing the proof.

<br/>

## Drill 7.8
### `(n : ℕ) (x : ℝ) (h₀: n = 0 → x = 0) (h₁: x = 19) : n ≠ 0`

- `by_contra h` begins a proof by contradiction. It assumes the exact opposite of the goal (assuming `n = 0`), assigns this assumption the name `h`, and changes the target goal to proving a mathematical impossibility (`False`).
- `have hx := h₀ h` feeds the newly assumed fact `h` (n = 0) into the implication rule `h₀` (n = 0 → x = 0). This correctly triggers the rule and generates the new factual deduction `hx : x = 0`.
- `linarith` scans the available hypotheses and spots the conflicting statements `hx` (`x = 0`) and `h₁` (`x = 19`). It combines these to deduce 0 = 19, yielding the required mathematical contradiction (`False`) and closing the proof.

<br/>

## Drill 7.9
### `(x y : ℝ) (h: 10 < x + y) : 5 < x ∨ 5 < y`

- The theorem asks to prove that if the sum of two numbers is strictly greater than 10, then at least one of the numbers must be strictly greater than 5.
- `by_contra! h₀` begins a proof by contradiction using the `!` variant to automatically simplify the negated logic. It negates the target `5 < x ∨ 5 < y`, applies De Morgan's laws to flip the OR (`∨`) to an AND (`∧`), and flips the inequalities. This assigns the new hypothesis `h₀ : x ≤ 5 ∧ y ≤ 5`.
- `linarith` scans the context for a contradiction. It automatically adds the two parts of `h₀` together to deduce that `x + y ≤ 10`. It then spots the direct conflict between this deduction and the original hypothesis `h : 10 < x + y`, yielding a mathematical contradiction and closing the proof.

<br/>

## Drill 7.10
### `(f : ℝ → ℝ) ( h : ¬ (∀ x : ℝ, f x ≤ 0)) : ∃ (x : ℝ), 1 < f x + 1`

- The theorem asks to prove that if it is false that all outputs of a function are ≤ 0, then there must exist some specific input x where f(x) + 1 > 1.
- `push Not at h` applies logical rules to push the negation inside the universal quantifier. It transforms the hypothesis `h : ¬(∀ x, f x ≤ 0)` into the positive existential statement `h : ∃ x, f x > 0`.
- `obtain ⟨k, hk⟩ := h` unwraps this existential hypothesis. It binds a specific real number variable `k` and adds the fact `hk : f k > 0` to local context.
- `use k` tells Lean to use this specific number `k` as the witness for the `∃ x` in the target goal. The goal updates from proving `∃ x, 1 < f x + 1` to proving specifically `1 < f k + 1`.
- `linarith` negates this goal, assuming `f k + 1 ≤ 1` (which simplifies internally to `f k ≤ 0`).
- It combines the negated goal (`f k ≤ 0`) with the hypothesis (`f k > 0`), yielding the mathematical contradiction `0 < 0`. This contradiction proves the original goal is true.
