# Calc And Linear Combination

* **Why `nlinarith` fails:** It relies on sorting inequalities to find a `0 < 0` contradiction. It crashes in abstract environments like `CommRing` or Complex Numbers (C) because these structures cannot be linearly ordered (e.g., 3 + 4i > 5 - 2i is mathematically undefined).
* **The Solution:** For pure equations (`=`) in these types, use **`ring`** or **`linear_combination`**. They solve proofs entirely through polynomial expansion and cancellation, bypassing the need for greater-than/less-than logic.
* **The Limitation:** `linear_combination` only supports linear operations. It balances equations by multiplying hypotheses by polynomial coefficients and adding them, but it cannot perform non-linear operations directly (like squaring a hypothesis).

<br/>

## Drill 5.1 (Three Approaches)

### `{R : Type*} [CommRing R] (x y : R) (h₁ : x + y = 7) (h₂ : x * y = 10) : x^2 + y^2 = 29`

- The generic `CommRing` context restricts the solver to pure algebraic equality (`=`). Tactics relying on inequalities (`linarith`, `nlinarith`) are invalid here since generic rings lack `<` or `≤` ordering.

- Approach 1: `linear_combination`

    - `linear_combination` internally normalizes the target goal to `x^2 + y^2 - 29 = 0` and hypotheses to `h1: x + y - 7 = 0` and `h₂: xy - 10 = 0`.
    - Expansion 1: Multiplies `h1` by `(x + y + 7)` to yield `(x + y)^2 - 49 = 0` (difference of squares).
    - Expansion 2: Multiplies `h₂` by `-2` to yield `-2xy + 20 = 0`.
    - The solver adds these expanded polynomial zeroes together. The `+2xy` and `-2xy` cancel, leaving exactly `x^2 + y^2 - 29 = 0`, automatically closing the goal.

- Approach 2: `rw` and `show`

    - `show x^2 + y^2 = (x + y)^2 - 2xy by ring` acts as an inline sub-proof. It uses `ring` to verify the algebraic identity without altering the context.
    - `rw [h1, h₂]` scans the modified goal for exact matches of the left-hand sides of the hypotheses, substituting `(x + y)` with `7` and `xy` with `10`.
    - `norm_num` evaluates the remaining numeric equation (`7^2 - 2 * 10 = 29`), normalizing both sides and closing the proof.

- Approach 3: `calc` block

    - `calc` structures the proof as a transitive chain of equalities, requiring each step to be individually justified.
    - Step 1 (`_ = (x + y)^2 - 2xy`): The `ring` tactic verifies the raw algebraic expansion matches the original `x^2 + y^2` term.
    - Step 2 (`_ = 29`): `rw [h1, h₂]` performs the substitution of known values (`7` and `10`), and `norm_num` acts as a calculator to compute `49 - 20 = 29`, successfully terminating the chain at the required goal.

<br/>

## Drill 5.2 (Three Approaches)

### `(z w : ℂ) (h₀ : z - w = 3) (h₁ : z * w = 4) : (z + w)^2 = 25`

- The `ℂ` (Complex Numbers) context restricts the solver to pure algebraic tools (`ring`, `linear_combination`). Tactics requiring inequalities (`linarith`, `nlinarith`) fail here because complex numbers cannot be linearly ordered.

- Approach 1: `linear_combination`

    - `linear_combination` targets the normalized goal `(z + w)^2 - 25 = 0` using the hypotheses `h₀: z - w - 3 = 0` and `h₁: zw - 4 = 0`.
    - Expansion 1: Multiplies `h₀` by `(z - w + 3)` to yield `(z - w)^2 - 9 = 0` (difference of squares).
    - Expansion 2: Multiplies `h₁` by `4` to yield `4zw - 16 = 0`.
    - The solver adds these expanded zeroes: `(z^2 - 2zw + w^2 - 9) + (4zw - 16)`. The `-2zw` and `+4zw` resolve to `+2zw`, perfectly reconstructing the normalized goal `(z + w)^2 - 25 = 0` and closing the proof.

- Approach 2: `rw` and `show`

    - `show (z + w)^2 = (z - w)^2 + 4(zw) by ring` generates an inline sub-proof. `ring` verifies this pure algebraic identity without looking at the hypotheses.
    - `rw [h₀, h₁]` scans the modified goal and explicitly substitutes `(z - w)` with `3` and `zw` with `4`.
    - `norm_num` normalizes the remaining arithmetic (`3^2 + 4 * 4 = 25`), balancing the equation and closing the goal.

- Approach 3: `calc` block

    - `calc` builds a transitive proof chain where each step is individually verified.
    - Step 1 (`_ = (z - w)^2 + 4(zw)`): The `ring` tactic verifies that this algebraic expansion is functionally identical to the initial `(z + w)^2` term.
    - Step 2 (`_ = 25`): `rw [h₀, h₁]` substitutes the known values (`3` and `4`), and `ring` acts as a computational calculator to evaluate `9 + 16 = 25`, successfully terminating the chain at the target integer.

<br/>

## Drill 5.3 (Three Approaches)

### `(x y : ℝ) (h₀: x + y = 4) (h₁: x * y = 2): x ^ 3 + y ^ 3 = 40`

- While real numbers (`ℝ`) support inequalities, this theorem is a pure algebraic equality (`=`). It is most efficiently solved using algebraic normalizers (`ring`, `linear_combination`, `norm_num`) rather than inequality-based contradiction tactics.

- Approach 1: `calc` block

    - `calc` structures the proof as a transitive chain of equivalencies.
    - Step 1 (`_ = (x + y)^3 - 3*(x*y)*(x + y)`): The `ring` tactic verifies that this algebraic expansion simplifies exactly to the original `x^3 + y^3`.
    - Step 2 (`_ = 40`): `rw [h₀, h₁]` actively replaces the isolated `(x + y)` terms with `4` and the `xy` term with `2`.
    - `norm_num` acts as a fast arithmetic evaluator, computing the pure numerical equation (`4^3 - 3 * 2 * 4 = 64 - 24 = 40`) and closing the chain.

- Approach 2: `rw` and `show`

    - `show x^3 + y^3 = (x + y)^3 - 3*(x*y)*(x + y) by ring` generates an inline sub-proof to verify the algebraic identity independent of the current context.
    - `rw [h₀, h₁]` scans the new goal and injects the numerical values from the hypotheses.
    - `norm_num` computes the remaining integer arithmetic, balancing the equation to `40 = 40` and closing the goal.

- Approach 3: `linear_combination`

    - `linear_combination` attempts to reconstruct the **normalized goal** (`x^3 + y^3 - 40 = 0`) directly from the hypotheses `h₀: x + y - 4 = 0` and `h₁: xy - 2 = 0`.
    - Expansion 1: Multiplies `h₀` by the complex polynomial coefficient `((x + y)^2 + 4*(x + y) + 10)`.
    - Expansion 2: Multiplies `h₁` by `-3*(x + y)`.
    - The internal solver adds these two expanded polynomial blocks together. All intermediate terms perfectly cancel out, leaving exactly `x^3 + y^3 - 40 = 0`. Since this mathematically matches the normalized goal, the proof is closed purely by algebraic addition.

<br/>

## Drill 5.4 (Two Approaches)

### `{R : Type*} [CommRing R] (x y z : ℝ) (h: x + y + z = 0) : x ^ 3 + y ^ 3 + z ^ 3 = 3 * x * y * z`

- Approach 1: `linear_combination`

    - `linear_combination` targets the **normalized goal** (`x^3 + y^3 + z^3 - 3xyz = 0`) using the hypothesis `h`: x + y + z = 0.
    - It multiplies `h` by the polynomial (`x^2 + y^2 + z^2 - xy - yz - zx`).
    - The solver internally expands this multiplication. All intermediate terms cancel out, leaving exactly `x^3 + y^3 + z^3 - 3xyz = 0`. Since this matches the normalized goal, the proof closes automatically.

- Approach 2: `have`, `linarith`, and `ring`

    - `have hk: z = -x - y := by linarith` generates a new local hypothesis (`hk`) by algebraically isolating z from x + y + z = 0. *(Note: `linarith` works here because the variables are explicitly typed as `ℝ` in the theorem signature).*
    * `rw [hk]` scans the main goal and replaces every instance of z with (-x - y).
    * `ring` evaluates the resulting two-variable equation: `x^3 + y^3 + (-x - y)^3 = 3xy(-x - y)`,  expands both sides, verifies they are algebraically identical, and closes the goal.

- The `calc` block requires explicitly writing out intermediate mathematical steps.
- `calc` for this specific identity would force us to manually write out the massive, visually cluttered expanded polynomial generated by substituting z = -x - y (e.g., -x^3 - 3x^2y - 3xy^2 - y^3) just to satisfy the transitive chain. Or we would have to remember a formula i.e. `x^3 + y^3 + z^3 - 3xyz = (x + y + z)(x^2 + y^2 + z^2 - xy - yz - zx)`.

<br/>

## Drill 5.5

### `(x : ℝ) (h: x ^ 2 = x + 1): x ^ 5 = 5 * x + 3`

- `linear_combination` targets the **normalized goal** (x^5 - 5x - 3 = 0) using the hypothesis `h`: x^2 - x - 1 = 0.
- It multiplies `h` by the exact polynomial coefficient (x^3 + x^2 + 2x + 3).
- The solver internally expands this multiplication. The x^4, x^3, and x^2 terms perfectly cancel each other out, leaving exactly x^5 - 5x - 3 = 0.Goal closed.

<br/>

## Drill 5.6

### `(x : ℝ) (h₀ : x ≠ 1) (h₁ : x^3 = 1) : x^2 + x + 1 = 0`

- `have h` uses `linear_combination h₁` to mathematically factor the hypothesis (x^3 - 1 = 0) into the algebraic identity `(x - 1) * (x^2 + x + 1) = 0`.
- `rcases mul_eq_zero.mp h` applies the zero-product property, splitting the equation into two logical cases (subgoals): `x - 1 = 0` OR `x^2 + x + 1 = 0`.
- **Case 1 (`x - 1 = 0`):** `linarith` algebraically deduces `x = 1`. The `contradiction` tactic then closes this branch by pointing out this violates the given hypothesis `h₀: x ≠ 1`.
- **Case 2 (`x^2 + x + 1 = 0`):** The remaining assumption perfectly matches the target goal, allowing `exact hk` to directly close the proof.

<br/>

## Drill 5.7 (Two Approaches)

### `(x y : ℝ) (h1 : x + y = 3) (h₂ : x * y = 1) : x^4 + y^4 = 47`

- Approach 1: `have` and `rw`

    - `have h` uses `ring` to generate a pure algebraic identity, factoring x^4 + y^4 entirely into instances of (x + y) and (xy): `((x + y)^2 - 2xy)^2 - 2(xy)^2`.
    - `rw [h, h1, h₂]` replaces the left side of the main goal with this identity, then substitutes (x + y) with 3 and xy with 1.
    - `norm_num` resolves the pure integer arithmetic (((3)^2 - 2 * 1)^2 - 2 * (1)^2 = 49 - 2 = 47) and closes the goal.

- Approach 2: `calc` block

    - Step 1 (`_ = (x^2 + y^2)^2 - 2(xy)^2`): `ring` verifies the first mathematical step, extracting the (xy) component.
    - Step 2 (`_ = ((x + y)^2 - 2xy)^2 - 2(xy)^2`): `ring` verifies the inner expansion, fully breaking down the remaining (x^2 + y^2) into (x + y) and (xy).
    - Step 3 (`_ = 47`): `rw [h1, h₂]` substitutes the known values from the hypotheses, and `norm_num` performs the final calculation to close the transitive chain.

- linear_combination requires to solve x^4 + y^4 - 47 = 0 using h1 (x + y - 3 = 0) and h₂ (xy - 1 = 0), the required polynomial multipliers would be massive and highly complex to calculate by hand.

<br/>

## Drill 5.8

### `(x y : ℝ) (h: x + y = 6): x * y ≤ 9`

- `have hk` establishes the intermediate bound `4 * x * y ≤ 36` using a `calc` chain.
- **Step 1 (`_ = (x + y)^2 - (x - y)^2`):** `nlinarith` verifies this fundamental algebraic identity.
- **Step 2 (`_ ≤ (x + y)^2`):** `nlinarith` proves this inequality by injecting the fact that squares are non-negative (`(x - y)^2 ≥ 0`), meaning subtracting it strictly decreases or maintains the value.
- **Step 3 (`_ = 36`):** `rw [h]` substitutes `(x + y)` with `6`, and `norm_num` computes `6^2 = 36`, successfully closing the `calc` chain for `hk`.
- With `hk: 4 * x * y ≤ 36` now verified in the local context, `linarith` trivially divides the inequality by 4 to close the main goal `x * y ≤ 9`.
