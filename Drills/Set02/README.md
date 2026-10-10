# Divisibility, Parity and Existentials
This is where we transition from basic algebraic manipulation into structural mathematical reasoning. In number theory, almost everything — `divisibility`, `even numbers`, `odd numbers` — is secretly an existential statement ("there exists an integer such that...").

Learning from this Set:
- The 4-Step Existential Rhythm: How to mechanically dismantle existential hypotheses and construct proofs using the `obtain` -> `use` -> `rw` -> `ring` pipeline.
- The Witness Principle: How to identify and provide the specific value (use) required to prove that something exists, distinguishing between what Lean can figure out and what requires mathematical intuition.

> [!Note]
> - `∃` requires a witness to prove the existence
> - `a ∣ b` reads as a divides b. Existential form : `∃ k, b = a * k`
> - `Even n` existential form is `∃ k, n = k + k`
> - `Odd n` existential form is `∃ k, n = 2 * k + 1`
> - For `∃`, `use` tactic provides a witness.
> - `a % b = c` reads as a divided by b leaves remainder c. Simplest form: `a = b * (a / b) + c`

<br/>

## Drill 2.1
### `∃ x : ℤ, 3 * x + 5 = 26`
- For `∃`, `use` tactic provides a witness.
- Here `7` is the witness. The goal changes to `3 * 7 + 5 = 26`
- `norm_num` stands for `normalised numbers`, it uses fundamental axioms of multiplication, addition and reflexivity (`=`) to close the goal.

> [!Note]
> We can directly use `omega` to resolve this as well (Caution: It won't work for anything other than simple linear equation). Covered Later.

<br/>

## Drill 2.2
### `(a b : ℤ) (h₀: ∃ k : ℤ, a = 4 * k + 1) (h₁: ∃ m : ℤ, b = 4 * m + 3) : ∃ n : ℤ, a + b = 4 * n`

- The `obtain` tactic unpacks the existential hypothesis `h₀`. It introduces a specific integer variable `k` into the local context and extracts the exact equation `a = 4 * k + 1`, assigning it the name `hk` and same for `h₁`.
- For `∃`, the `use` tactic provides a witness.
- Here `k + m + 1` is the witness. The goal changes to `a + b = 4 * (k + m + 1)`.
- `rw [hk, hm]` substitutes the variables using the extracted equalities, transforming the goal into `(4 * k + 1) + (4 * m + 3) = 4 * (k + m + 1)`.
- `ring` evaluates both sides of the polynomial equation and closes the goal automatically.

> [!Note]
> The `ring` tactic is provided by Mathlib specifically for commutative rings (like integers). It automatically handles associativity, commutativity, and distributivity so we don't have to manually factor or rearrange the terms.


<br/>

## Drill 2.3
### `(x : ℤ) (h₀: ∃ k, x = 3 * k + 2) : ∃ m, x ^ 2 = 3 * m + 1`

- `obtain ⟨k, hk⟩ := h₀`
    - The `obtain` tactic unpacks the existential hypothesis `h₀`. It introduces a specific integer variable `k` into the local context and extracts the exact equation `x = 3k + 2`, assigning it the name `hk`.
- `use 3 * k ^ 2 + 4 * k + 1`
    - The goal is to prove `∃ m, x ^ 2 = 3 * m + 1`. The `use` tactic provides a direct witness for this existential quantifier. By telling Lean to use `3k^2 + 4k + 1` for `m`, the goal updates to proving the specific equality: `x^2 = 3 * (3k^2 + 4k + 1) + 1`.
- `rw[hk]`
    - `rw` (rewrite) tactic substitutes variables. Goal transforms into: `(3k + 2)^2 = 3(3k^2 + 4k + 1) + 1`.
- `ring`
    - Recognizes structural equivalence (`=`) and closes the proof.

<br/>

## Drill 2.4
### `(n : ℤ) (h₀: 5 ∣ n) : 5 ∣ (n ^ 2 + 10 * n)`

- `obtain ⟨k, hk⟩ := h₀`
    - This unpacks the definition of divisibility from hypothesis h₀. It tells Lean: "Since `5 ∣ n`, there must exist some integer `k` such that `n = 5k`." It introduces this new integer `k` into the local context and names the equation `n = 5k` as a new hypothesis `hk`.
- `use 5 * k ^ 2 + 10 * k`
    - The goal is to prove  `5 ∣ (n^2 + 10n)` , which Lean understands mathematically as finding a "witness" value `c` such that  `n^2 + 10n = 5c` . The use tactic provides that exact witness. Lean now changes the goal to proving the equality:  `n^2 + 10n = 5(5k^2 + 10k)` .
- `rw[hk]`
    - The `rw` (rewrite) tactic looks at the equation in hypothesis `hk` `( n = 5k )` and replaces every instance of  `n`  in the goal with  `5k` . The goal updates to:  `(5k)^2 + 10(5k) = 5(5k^2 + 10k)` .
- `ring`
    - Expands, groups, and simplifies both sides of the equation algebraically. Since both sides simplify to  `25k^2 + 50k` , ring recognizes they are mathematically identical and closes the proof.

## Drill 2.5
### `(a b c : ℤ) (h₀: c ∣ a ∧ c ∣ b) : c ∣ (3 * a - 5 * b)`

- `h₀.left` and `h₀.right` split the `∧` (AND) hypothesis into `c ∣ a` and `c ∣ b`.
- `obtain` unpacks their hidden existential form (`∃ k, a = c * k`). `c ∣ a` yields a witness `k` and hypothesis `hk : a = c * k`. `c ∣ b` yields `m` and `hm : b = c * m`.
- The goal `c ∣ (3 * a - 5 * b)` unfolds internally as `∃ x, 3 * a - 5 * b = c * x`.
- `use 3 * k - 5 * m` provides the required witness for `x`, transforming the goal into `3 * a - 5 * b = c * (3 * k - 5 * m)`.
- `rw[hk, hm]` substitutes `a` and `b`, updating the goal to `3 * (c * k) - 5 * (c * m) = c * (3 * k - 5 * m)`.
- `ring` automatically expands and verifies this algebraic equality using the axioms of a commutative ring, closing the goal.

<br/>

## Drill 2.6
### `(a b c : ℤ) (h₀: a ∣ b) (h₁: b ∣ c) : a ∣ c`

- `obtain` unpacks the hidden existential forms for both hypotheses. `h₀: a ∣ b` yields a witness `k` and hypothesis `hk : b = a * k`. `h₁: b ∣ c` yields a witness `m` and hypothesis `hm : c = b * m`.
- The goal `a ∣ c` unfolds internally as `∃ x, c = a * x`.
- `use k * m` provides the required witness for `x`, transforming the goal into `c = a * (k * m)`.
- `rw [hm, hk]` sequentially substitutes `c` with `b * m` (from `hm`), and then `b` with `a * k` (from `hk`), updating the goal to `(a * k) * m = a * (k * m)`.
- `ring` automatically verifies this algebraic equality using the associative property of multiplication in a commutative ring, closing the goal.

> [!Note]
> A transitivity lemma already exists in the library for this!

<br/>

## Drill 2.7
### `(n : ℤ) : 3 ∣ (n + (n + 1) + (n + 2))`

- The goal `3 ∣ (n + (n + 1) + (n + 2))` unfolds internally as an existential statement: `∃ x, n + (n + 1) + (n + 2) = 3 * x`.
- `use n + 1` provides the required witness for `x`, transforming the goal into the algebraic equation `n + (n + 1) + (n + 2) = 3 * (n + 1)`.
- `ring` automatically expands, simplifies, and verifies this algebraic equality (recognizing both sides equal `3 * n + 3`), closing the goal.

<br/>

## Drill 2.8
### `(n : ℤ) (h₀ : Odd n) : 4 ∣ (n ^ 2 - 1)`

- `obtain` unpacks the existential definition of an odd number from the hypothesis. `h₀ : Odd n` yields a witness `k` and hypothesis `hk : n = 2 * k + 1`.
- The goal `4 ∣ (n ^ 2 - 1)` unfolds internally as `∃ x, n ^ 2 - 1 = 4 * x`.
- `use k ^ 2 + k` provides the required witness for `x`, transforming the goal into `n ^ 2 - 1 = 4 * (k ^ 2 + k)`.
- `rw[hk]` substitutes `n` with `2 * k + 1`, updating the goal to `(2 * k + 1) ^ 2 - 1 = 4 * (k ^ 2 + k)`.
- `ring` automatically expands the polynomial `(2 * k + 1) ^ 2 - 1` to `4 * k ^ 2 + 4 * k` and verifies it equals the right side `4 * (k ^ 2 + k)`, closing the goal.

<br/>

## Drill 2.9
### `(a b : ℤ) (h₀ : Even a) (h₁ : Odd b) : Odd (a + b)`

- `obtain` unpacks the existential definitions from both hypotheses. `h₀ : Even a` yields a witness `k` and hypothesis `hk : a = k + k`. `h₁ : Odd b` yields a witness `m` and hypothesis `hm : b = 2 * m + 1`.
- The goal `Odd (a + b)` unfolds internally as `∃ x, a + b = 2 * x + 1`.
- `use k + m` provides the required witness for `x`, transforming the goal into `a + b = 2 * (k + m) + 1`.
- `rw [hk, hm]` substitutes `a` and `b` using the unpacked hypotheses, updating the goal to `k + k + (2 * m + 1) = 2 * (k + m) + 1`.
- `ring` automatically expands, regroups, and verifies this algebraic equality, closing the goal.

<br/>

## Drill 2.10
### `(n : ℕ) (h₀ : n % 6 = 4) : n % 3 = 1`

- `omega` relies strictly on quantifier-free integer linear arithmetic, meaning it actively avoids explicit `∃` searches.
- To handle the non-linear `%` operator, it uses the built-in integer division axiom: `n = c  * (n / c) + n % c` .
- It translates `h₀` into `n = 6  * (n / 6) + 4`. It treats the quotient  `(n / 6)`  as a rigid, hidden variable (let's call it  `q` ), feeding the flat equation  `n = 6q + 4`  to its solver.
- Substituting this into the goal evaluates  `(6q + 4) % 3` . The linear solver recognizes  `6q`  is perfectly divisible by  `3` , reducing the expression entirely to  `4 % 3` , which evaluates to  `1` , closing the goal automatically.