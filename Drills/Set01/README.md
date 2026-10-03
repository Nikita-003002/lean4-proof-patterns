# Non-Linear bounding and Linarith
This set specifically focuses on extra addons required to feed tactics to solve the given step efficiently.

> [!NOTE]
> `linarith` only understands linear terms. Whenever a problem involves squares (x ^ ), products (x * y), or absolute values (| x |), manually state a non-negative fact using `have` and feed it inside the brackets `linarith [...]`.

## Drill 1.1
### `(x : ℝ) : x ^ 2 - 5 ≥ -5`

- `sq_nonneg` unfolds as `∀ a, 0 ≤ a ^ 2`

- Internally, it substitutes `x^2` with a fresh placeholder variable, say `A`.

- Hypothesis becomes `A ≥ 0, A - 5 ≥ -5`.

- linarith always works by refutation (contradiction). It assumes the negation of the goal is true and tries to derive 0 < 0 (False). So by that, goal becomes `A - 5 < -5` .

- `A ≥ 0` rearranges to (no negation is assumed here) `-A ≤ 0`.
- `A - 5 < -5` rearranges to `A < 0`.
- linarith searches for non-negative multiplier `(-A ≤ 0) and (A < 0)` and add it yielding `0 < 0` which is obviously false and closing the goal.


