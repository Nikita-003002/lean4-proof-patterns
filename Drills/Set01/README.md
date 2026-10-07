# Non-Linear bounding and Linarith
This set specifically focuses on extra addons required to feed tactics to solve the given step efficiently.

> [!NOTE]
> `linarith` only understands linear terms. Whenever a problem involves squares (x ^ 2), products (x * y), or absolute values (| x |), manually state a non-negative fact using `have` and feed it inside the brackets `linarith [...]`.

</br>

## Drill 1.1
### `(x : ℝ) : x ^ 2 - 5 ≥ -5`

- `sq_nonneg x` unfolds as `∀ x, 0 ≤ x ^ 2`
- Internally, it substitutes `x^2` with a fresh placeholder variable, say `A`.
- Hypothesis becomes `A ≥ 0, A - 5 ≥ -5`.
- linarith always works by refutation (contradiction). It assumes the negation of the goal is true and tries to derive 0 < 0 (False). So by that, goal becomes `A - 5 < -5` .
- `A ≥ 0` rearranges to (no negation is assumed here) `-A ≤ 0`.
- `A - 5 < -5` rearranges to `A < 0`.
- linarith searches for non-negative multiplier `(-A ≤ 0) and (A < 0)` and add it yielding `0 < 0` which is obviously false and closing the goal.

</br>

## Drill 1.2
### `(x : ℝ) : 6 * x - 9 ≤ x ^ 2`

- `sq_nonneg (x - 3)` unfolds as `0 ≤ (x - 3) ^ 2`
- `ring` formalization from `0 ≤ (x - 3) ^ 2` to `0 ≤ x ^ 2 - 6 * x + 9`.
- `h1: 0 ≤ A - 6 * x + 9` and `Goal: 6 * x - 9 ≤ A`
- forming `0 < 0` for linarith.
- Negating the goal to `6 * x - 9 > A`. 
- Rearranging Goal to rhs standard format `(expression < 0)`  `A - 6 * x + 9 < 0`.
- Rearranging h1 to rhs standard format `-A + 6 * x - 9 ≤ 0`.
- Addind Goal and h1 yields `0 < 0`

</br>

## Drill 1.3
### `2 * a * b ≤ a ^ 2 + b ^ 2`

- Same as above drill but with three different variable instead of just one.
- `a^2` say `A`, `b^2` say `B` and `2 * a * b` say `C`.

</br>

## Drill 1.4
### `(a b c : ℝ) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2`

- `sq_nonneg (a - b)`, `sq_nonneg (b - c)`, and `sq_nonneg (c - a)` unfold as `0 ≤ (a - b) ^ 2`, `0 ≤ (b - c) ^ 2`, and `0 ≤ (c - a) ^ 2`.
- `ring` normalization expands them into `0 ≤ a ^ 2 - 2 * a * b + b ^ 2`, `0 ≤ b ^ 2 - 2 * b * c + c ^ 2`, and `0 ≤ c ^ 2 - 2 * c * a + a ^ 2`.
- Substituting non-linear terms (`A = a^2`, `B = b^2`, `C = c^2`, `X = a*b`, `Y = b*c`, `Z = c*a`) gives:
  - `h1: 0 ≤ A - 2 * X + B`
  - `h2: 0 ≤ B - 2 * Y + C`
  - `h3: 0 ≤ C - 2 * Z + A`
  - `Goal: X + Y + Z ≤ A + B + C`
- Forming `0 < 0` for `linarith`:
- Negating the goal to `X + Y + Z > A + B + C`.
- Rearranging Goal to standard format `(expression < 0)`: `A + B + C - X - Y - Z < 0`.
- Rearranging `h1`, `h2`, and `h3` to standard format `(expression ≤ 0)`:
  - `h1: -A + 2 * X - B ≤ 0`
  - `h2: -B + 2 * Y - C ≤ 0`
  - `h3: -C + 2 * Z - A ≤ 0`
- Adding `h1 + h2 + h3` gives `-2 * A - 2 * B - 2 * C + 2 * X + 2 * Y + 2 * Z ≤ 0`.
- Multiplying the negated Goal by `2` gives `2 * A + 2 * B + 2 * C - 2 * X - 2 * Y - 2 * Z < 0`.
- Adding `2 * Goal` and `h1 + h2 + h3` yields `0 < 0`.

</br>

## Drill 1.5
### `(x y : ℝ) (h₀: y = 19 + |x|) : 19 ≤ y`

- `abs_nonneg x` unfolds as `0 ≤ |x|`.
- Substituting the non-linear term (`A = |x|`) gives:
  - `h₀: y = 19 + A`
  - `h1: 0 ≤ A`
  - `Goal: 19 ≤ y`
- Forming `0 < 0` for `linarith`:
- Negating the goal to `19 > y`.
- Rearranging Goal to standard format `(expression < 0)`: `y - 19 < 0`.
- Rearranging `h₀` and `h1` to standard format `(expression ≤ 0)`:
  - `h₀: -y + A + 19 ≤ 0` (derived from `y = 19 + A`)
  - `h1: -A ≤ 0`
- Adding `Goal + h₀ + h1` cancels `y`, `A`, and `19`, yielding `0 < 0`.

</br>

## Drill 1.6
### `(a b c : ℝ) (h₀: c = 10 + |a - 1| + |b - 2|) : 10 ≤ c`

- `abs_nonneg (a - 1)` unfolds as `0 ≤ |a - 1|`, and `abs_nonneg (b - 2)` unfolds as `0 ≤ |b - 2|`.
- Substituting the non-linear terms (`A = |a - 1|` and `B = |b - 2|`) gives:
  - `h₀: c = 10 + A + B`
  - `h1: 0 ≤ A`
  - `h2: 0 ≤ B`
  - `Goal: 10 ≤ c`
- Forming `0 < 0` for `linarith`:
- Negating the goal to `10 > c`.
- Rearranging Goal to standard format `(expression < 0)`: `c - 10 < 0`.
- Rearranging `h₀`, `h1`, and `h2` to standard format `(expression ≤ 0)`:
  - `h₀: -c + A + B + 10 ≤ 0` (derived from `c = 10 + A + B`)
  - `h1: -A ≤ 0`
  - `h2: -B ≤ 0`
- Adding `Goal + h₀ + h1 + h2` cancels `c`, `A`, `B`, and `10`, yielding `0 < 0`.

</br>

## Drill 1.7
### `(x S : ℝ) (h₀: S = 19 + |x|) (h₁: S < 25) : 19 ≤ S ∧ |x| < 6`

- `constructor` splits the conjunction (`∧`) goal into two separate subgoals: `Goal 1: 19 ≤ S` and `Goal 2: |x| < 6`.
- `abs_nonneg x` unfolds as `0 ≤ |x|`.
- Substituting the non-linear term (`A = |x|`) gives:
  - `h₀: S = 19 + A`
  - `h₁: S < 25`
  - `h2: 0 ≤ A` (used in Subgoal 1)

- **Subgoal 1 (`19 ≤ S`):**
  - Forming `0 < 0` for `linarith`:
  - Negating the goal to `19 > S`.
  - Rearranging Goal 1 to standard format `(expression < 0)`: `S - 19 < 0`.
  - Rearranging `h₀` and `h2` to standard format `(expression ≤ 0)`:
    - `h₀: -S + A + 19 ≤ 0` (derived from `S = 19 + A`)
    - `h2: -A ≤ 0`
  - Adding `Goal 1 + h₀ + h2` cancels `S`, `A`, and `19`, yielding `0 < 0`.

- **Subgoal 2 (`|x| < 6`, i.e., `A < 6`):**
  - Forming `0 < 0` for `linarith`:
  - Negating the goal to `A ≥ 6`.
  - Rearranging Goal 2 to standard format `(expression ≤ 0)`: `-A + 6 ≤ 0`.
  - Rearranging `h₀` and `h₁` to standard format:
    - `h₀: -S + A + 19 ≤ 0` (derived from `S = 19 + A`)
    - `h₁: S - 25 < 0`
  - Adding `Goal 2 + h₀ + h₁` cancels `A`, `S`, and the constants (`6 + 19 - 25 = 0`), yielding `0 < 0`.

  </br>

## Drill 1.8
### `(x y : ℝ) (h₀: |x - 3| ≤ 2) (h₁: y = x + 5) : 6 ≤ y`

- `abs_le.mp h₀` unfolds `|x - 3| ≤ 2` as `-2 ≤ x - 3 ∧ x - 3 ≤ 2`.
- Splitting the conjunction (`∧`) gives the linear system:
  - `h₁: y = x + 5`
  - `h2: -2 ≤ x - 3`
  - `h3: x - 3 ≤ 2` (unused)
  - `Goal: 6 ≤ y`
- Forming `0 < 0` for `linarith`:
- Negating the goal to `6 > y`.
- Rearranging Goal to standard format `(expression < 0)`: `y - 6 < 0`.
- Rearranging `h₁` and `h2` to standard format `(expression ≤ 0)`:
  - `h₁: x - y + 5 ≤ 0` (derived from `y = x + 5`)
  - `h2: -x + 1 ≤ 0` (derived from `-2 ≤ x - 3`)
- Adding `Goal + h₁ + h2` cancels `y`, `x`, and constants (`-6 + 5 + 1`), yielding `0 < 0`.

</br>

## Drill 1.9
### `(x y : ℝ) (h₀: x ≥ 1 ∧ y ≥ 1) : x + y ≤ x * y + 1`

- **`linarith` / `nlinarith` automatically splits conjunctions (`∧`) in hypotheses:** `h₀` is unpacked into `h1: 1 ≤ x` and `h2: 1 ≤ y` (i.e., `0 ≤ x - 1` and `0 ≤ y - 1`) without needing `rcases` or `.1` / `.2`.
- **`nlinarith` automatically multiplies pairwise non-negative terms:** `0 ≤ (x - 1) * (y - 1)`, which expands to `0 ≤ x * y - x - y + 1`.
- Substituting the non-linear term (`A = x * y`) gives:
  - `h1: 1 ≤ x`
  - `h2: 1 ≤ y`
  - `h3: 0 ≤ A - x - y + 1`
  - `Goal: x + y ≤ A + 1`
- Forming `0 < 0` for `linarith`:
- Negating the goal to `x + y > A + 1`.
- Rearranging Goal to standard format `(expression < 0)`: `A - x - y + 1 < 0`.
- Rearranging `h3` to standard format `(expression ≤ 0)`:
  - `h3: -A + x + y - 1 ≤ 0` (derived from `0 ≤ A - x - y + 1`)
- Adding `Goal + h3` cancels `A`, `x`, `y`, and `1`, yielding `0 < 0`.

</br>

## Drill 1.10
### `(x y : ℝ) (h₀: y > 0) : 0 < (x ^ 2 + 1) / y + |y|`

- `positivity` builds an Abstract Syntax Tree (AST), breaking the goal into leaves, evaluating their signs, and rolling them back up to the root.
- **Top-Level Split (Root Node):** Evaluates the addition `A + B`, where `A = (x ^ 2 + 1) / y` and `B = |y|`.
- **Evaluating the right branch (`B = |y|`):**
  - The absolute value extension applies `abs_nonneg y`, yielding `0 ≤ |y|`.
- **Evaluating the left branch (`A = (x ^ 2 + 1) / y`):**
  - The denominator `y` is flagged as strictly positive from the local context `h₀: y > 0`.
  - The numerator is split into an addition sub-tree `C + D`, where `C = x ^ 2` and `D = 1`:
    - The squares extension applies `sq_nonneg x`, yielding `0 ≤ x ^ 2`.
    - The numeric literal `1` trivially yields `0 < 1`.
    - Rolling up the numerator: Adding `0 ≤ x ^ 2` and `0 < 1` yields `0 < x ^ 2 + 1`.
  - Rolling up the division: Dividing the strictly positive numerator by the strictly positive denominator yields `0 < (x ^ 2 + 1) / y`.
- **Combining the evaluated branches:**
  - Left branch: `0 < (x ^ 2 + 1) / y`
  - Right branch: `0 ≤ |y|`
- **Final Roll-Up:** Adding `Strictly Positive + Non-negative` yields the final closed goal `0 < (x ^ 2 + 1) / y + |y|`.
