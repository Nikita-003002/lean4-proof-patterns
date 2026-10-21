# Denominators, Roots

- Lean will not let us multiply out denominators unless it is mathematically guaranteed they are not zero. Tactics like `field_simp` flatten fractions into standard algebra, but we must pass them non-zero proofs (e.g., `field_simp [h]`) unless the denominator is obviously strictly positive (like `x^2 + 1`).
- When working with inequalities, clearing a denominator requires knowing its exact sign. If the denominator is negative, we must use specific lemmas (like `div_le_iff_of_neg`) combined with the negative hypothesis to safely clear the fraction and automatically flip the inequality's direction.
- Lean treats square roots rigorously. To simplify terms like `(√x)^2 = x` using lemmas such as `Real.sq_sqrt`, we must always provide explicit proof that the term inside the root is non-negative (`0 ≤ x`), either from the context hypotheses or via a quick inline proof like `(by linarith)`.

<br/>

## Drill 8.1
### `(a b : ℝ) (h : a ≠ 0 ∧ b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b)`

- `field_simp` is a tactic designed specifically to simplify expressions containing fractions.
- `[h]` passes the hypothesis (`a ≠ 0 ∧ b ≠ 0`) to `field_simp`.
- Lean requires this non-zero proof to mathematically justify multiplying out the denominators.
- After `field_simp [h]` runs, the fractions are cleared. The goal transforms into a flat algebraic equation (effectively `b + a = a + b`).
- `ring` applies commutativity (`b + a` to `a + b`) and closes the goal.

<br/>

## Drill 8.2
### `(x : ℝ) : x^2 / (x^2 + 1) + 1 / (x^2 + 1) = 1`

- `field` is an all-in-one tactic that solves universal equality goals in fields by handling both fractions and polynomial algebra simultaneously.
- Under the hood, it automatically runs `field_simp` to clear denominators, followed by `ring` to prove the resulting algebraic identity.
- To legally clear fractions, Lean needs proof that the denominators aren't zero. The `field` tactic includes a built-in "discharger" algorithm that automatically attempts to prove this behind the scenes.
- For the denominator `x^2 + 1` over the real numbers (`ℝ`), the default discharger successfully proves it is never zero (using order properties like `x^2 ≥ 0`), requiring no manual `[h]` hypotheses from us.
- With the denominator mathematically validated and cleared, the tactic reduces the goal to a fraction-free equation (`x^2 + 1 = x^2 + 1`) and instantly closes it.

<br/>

## Drill 8.3
### `(x : ℝ) (h: x ≠ 2 ∧ x ≠ -2) : 1 / (x - 2) - 1 / (x + 2) = 4 / (x^2 - 4)`

- `have h₀: x - 2 ≠ 0 := sub_ne_zero.mpr h.1` creates a new hypothesis. It takes `x ≠ 2` from the first half of `h` (`h.1`) and uses the `sub_ne_zero` lemma to mathematically translate it into `x - 2 ≠ 0`.
- `have h₁: x + 2 ≠ 0 := by ...` opens a mini-proof to establish the second denominator is non-zero. It assumes the opposite via `intro h_zero` (`x + 2 = 0`) and feeds it to `linarith`, which derives a contradiction against `h.2` (`x ≠ -2`).
- `rw [show x^2 - 4 = (x - 2) * (x + 2) by ring]` replaces the quadratic denominator with its factored form. The inline `show ... by ring` proves this difference-of-squares identity on the spot so `rw` can substitute it into the goal.
- `field_simp [h₀, h₁]` targets the fractional expression. By explicitly passing our new `h₀` and `h₁` proofs, we give Lean the mathematical justification needed to safely multiply out the non-zero denominators `(x - 2)` and `(x + 2)`.
- `ring` takes over once the denominators are cleared. It processes the resulting flat algebraic equation, expanding and canceling terms to prove both sides are identical, instantly closing the goal.

<br/>

## Drill 8.4
### `(x y : ℝ) (h₀ : x ≠ 0 ∧ y ≠ 0) (h₁ : 1 / x + 1 / y = 5) (h₂ : x + y = 10) : x * y = 2`

- `field_simp [h₀] at h₁` targets the fractional addition, but applies it directly to the hypothesis `h₁` instead of the main goal.
- `[h₀]` provides the necessary proofs that `x` and `y` are non-zero, mathematically justifying clearing the denominators in `h₁`.
- This step transforms the fraction-based hypothesis `h₁` (`1 / x + 1 / y = 5`) into a flat, fraction-free equation: `x + y = 5 * (x * y)`.
- `linarith` assumes the negation of the goal (`x * y ≠ 2`), then evaluates the transformed `h₁` (`x + y = 5 * (x * y)`) alongside `h₂` (`x + y = 10`).
- By substituting `h₂` into `h₁`, it effectively sees `10 = 5 * (x * y)` (which forces `x * y = 2`). Combining this mathematical fact with the negated goal yields a logical contradiction , which closes the goal.

<br/>

## Drill 8.5
### `(a b : ℝ) (h₀ : 0 < b) (h₁: a / b ≤ 3) : a ≤ 3 * b`

- `field_simp at h₁` targets the fractional inequality, applying the simplification directly to the hypothesis `h₁` instead of the main goal.
- Lean automatically uses the `h₀ : 0 < b` hypothesis from the context to mathematically justify clearing the strictly positive denominator `b` without flipping the inequality.
- This step transforms the fraction-based hypothesis `h₁` (`a / b ≤ 3`) into a flat, fraction-free inequality: `a ≤ 3 * b`.
- `linarith` assumes the negation of the main goal (`a > 3 * b`).
- It compares this negated goal directly against the newly transformed hypothesis `h₁` (`a ≤ 3 * b`), yielding an immediate logical contradiction, which closes the goal.

<br/>

## Drill 8.6
### `(x : ℝ) (h: 0 < x) : 2 ≤ x + 1 / x`

- `field_simp` targets the fractional inequality in the main goal.
- Lean automatically uses the `h : 0 < x` hypothesis to mathematically justify clearing the strictly positive denominator `x` without altering the inequality direction.
- This step transforms goal (`2 ≤ x + 1 / x`) into `2 * x ≤ x^2 + 1`.
* `linarith [sq_nonneg (x - 1)]` assumes the negation of this new goal (`2 * x > x^2 + 1`, which algebraically rearranges to `x^2 - 2 * x + 1 < 0`).
* It evaluates this negated goal alongside the explicitly provided mathematical fact `sq_nonneg (x - 1)` (which asserts that any square is non-negative: `0 ≤ x^2 - 2 * x + 1`).
* Combining the negated goal with this provided fact yields a direct logical contradiction, which closes the goal.

<br/>

## Drill 8.7
### `(x : ℝ) : 2 * x / (x ^ 2 + 1) ≤ 1`

- `field_simp` targets the fractional inequality in the main goal.
- Lean automatically recognizes that the denominator `x^2 + 1` is strictly positive (since `x^2 ≥ 0`), mathematically justifying clearing the fraction without an explicit hypothesis or altering the inequality direction.
- This step transforms the goal (`2 * x / (x^2 + 1) ≤ 1`) into `2 * x ≤ x^2 + 1`.
- `linarith [sq_nonneg (x - 1)]` assumes the negation of this new goal (`2 * x > x^2 + 1`, which algebraically rearranges to `x^2 - 2 * x + 1 < 0`).
- It evaluates this negated goal alongside the explicitly provided mathematical fact `sq_nonneg (x - 1)` (which asserts that any square is non-negative: `0 ≤ x^2 - 2 * x + 1`).
- Combining the negated goal with this provided fact yields a direct logical contradiction, which closes the goal.

<br/>

## Drill 8.8
### `(x : ℝ) (h₀: 0 ≤ x) : (√x + 1) ^ 2 = x + 2 * √x + 1`

- `ring_nf` expands the algebraic expression, treating the square root term (`√x`) as a standard opaque variable.
- This step transforms the goal from `(√x + 1) ^ 2 = x + 2 * √x + 1` into its expanded algebraic form: `(√x) ^ 2 + 2 * √x + 1 = x + 2 * √x + 1`.
- `rw [Real.sq_sqrt h₀]` applies the lemma `Real.sq_sqrt`, using the explicit hypothesis `h₀ : 0 ≤ x` to mathematically justify that `(√x)^2 = x`.
- This substitution replaces `(√x)^2` with `x` in the goal, making both sides perfectly identical and automatically closing the goal via reflexivity.

<br/>

## Drill 8.9
### `(x : ℝ) (h : 3 ≤ x) : √(x - 3) ^ 2 = x - 3`

- `rw [Real.sq_sqrt ...]` applies the `Real.sq_sqrt` lemma to simplify the squared square root expression (which asserts that `(√A)^2 = A` as long as `0 ≤ A`).
- To mathematically justify this simplification, the lemma requires an explicit proof that the inner term is non-negative (`0 ≤ x - 3`).
- The inline tactic `(by linarith)` automatically generates this prerequisite proof on the fly by algebraically rearranging the provided hypothesis `h : 3 ≤ x` into `0 ≤ x - 3`.
- With the non-negativity condition satisfied, `rw` replaces `√(x - 3) ^ 2` with `x - 3`. This leaves both sides perfectly identical (`x - 3 = x - 3`), automatically closing the goal via reflexivity.

<br/>

## Drill 8.10
### `(a b : ℝ) (h : 0 ≤ a ∧ 0 ≤ b) : √(a * b) ≤ (a + b) / 2`

- `rw [Real.sqrt_mul h.1]` applies the rule that the square root of a product equals the product of square roots (`√(a * b) = √a * √b`). It uses `h.1` (`0 ≤ a`) to mathematically justify this split, transforming the goal into `√a * √b ≤ (a + b) / 2`.
- `have h₀: (√a - √b) ^ 2 = a + b - 2 * √a * √b` introduces a new algebraic identity. Inside the mini-proof, `ring_nf` expands the squared binomial, and `rw [Real.sq_sqrt...]` uses the non-negativity hypotheses to simplify `(√a)^2` and `(√b)^2` into `a` and `b`.
- `have h₁: 0 ≤ a + b - 2 * √a * √b` establishes that this expanded polynomial is non-negative. It proves this by rewriting it backwards (`← h₀`) into the squared form `(√a - √b)^2`, which the `positivity` tactic instantly recognizes and proves is strictly `≥ 0`.
- `linarith` assumes the negation of the current goal (`√a * √b > (a + b) / 2`, which algebraically rearranges to `a + b - 2 * √a * √b < 0`).
- It evaluates this negated goal directly against the newly proven mathematical fact `h₁` (`0 ≤ a + b - 2 * √a * √b`).
- Combining the negated goal with `h₁` yields a direct logical contradiction, which closes the goal.

<br/>

## Drill 8.11
### `(a b : ℝ) (h₀: b < 0) (h₁: a / b ≤ 5) : 15 * b ≤ 3 * a`

- `rw [div_le_iff_of_neg h₀] at h₁` targets the fractional inequality in hypothesis `h₁`.
- Lean uses the explicitly provided `h₀ : b < 0` hypothesis to mathematically justify clearing the strictly negative denominator `b`.
- Because the denominator is negative, this specific lemma automatically flips the inequality's direction, transforming the hypothesis `h₁` (`a / b ≤ 5`) into `5 * b ≤ a`.
- `linarith` assumes the negation of the main goal (`15 * b > 3 * a`, which algebraically simplifies to `5 * b > a`).
- It evaluates this negated goal directly against the newly transformed hypothesis `h₁` (`5 * b ≤ a`).
- Combining the negated goal with `h₁` yields a direct logical contradiction, which closes the goal.

<br/>

## Drill 8.12
### `(a b c : ℝ) (h₀: b < 0) (h₁: a / b < c) : c * b < a`

- `rw [div_lt_iff_of_neg h₀] at h₁` targets the strict fractional inequality in hypothesis `h₁`.
- Lean uses the explicitly provided `h₀ : b < 0` hypothesis to mathematically justify clearing the strictly negative denominator `b`.
- Because the denominator is negative, this specific lemma automatically flips the strict inequality's direction, transforming the hypothesis `h₁` (`a / b < c`) into `c * b < a`.
- `exact h₁` tells Lean that the newly transformed hypothesis `h₁` is now perfectly identical to the main goal (`c * b < a`), which closes the proof.

<br/>

## Drill 8.13

### `(x y z : ℝ) (h : 0 < y) : (x / y ≤ z) ↔ (x ≤ z * y)`

- `div_le_iff₀` is a Mathlib lemma that establishes a direct logical equivalence (`↔`) between a fractional inequality and its fraction-free counterpart.
- `h` is passed to the lemma to satisfy its prerequisite, proving that the denominator `y` is strictly positive (`0 < y`).
- This mathematically justifies clearing the denominator across the inequality by multiplying both sides by `y` without flipping the inequality direction.
- `exact` tells Lean that this fully resolved lemma perfectly matches the entire target equivalence goal, closing the proof.
