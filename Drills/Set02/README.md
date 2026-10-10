# Divisibility, Parity and Existentials
This is where we transition from basic algebraic manipulation into structural mathematical reasoning. In number theory, almost everything — `divisibility`, `even numbers`, `odd numbers` — is secretly an existential statement ("there exists an integer such that...").

Learning from this Set:
- The 4-Step Existential Rhythm: How to mechanically dismantle existential hypotheses and construct proofs using the `obtain` -> `use` -> `rw` -> `ring` pipeline.
- The Witness Principle: How to identify and provide the specific value (use) required to prove that something exists, distinguishing between what Lean can figure out and what requires mathematical intuition.

> [!Note]
> `∃` requires a witness to prove the existence

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

# Drill 2.3
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

# Drill 2.4
## `(n : ℤ) (h₀: 5 ∣ n) : 5 ∣ (n ^ 2 + 10 * n)`

- `obtain ⟨k, hk⟩ := h₀`
    - This unpacks the definition of divisibility from hypothesis h₀. It tells Lean: "Since `5 ∣ n`, there must exist some integer `k` such that `n = 5k`." It introduces this new integer `k` into the local context and names the equation `n = 5k` as a new hypothesis `hk`.
- `use 5 * k ^ 2 + 10 * k`
    - The goal is to prove  `5 ∣ (n^2 + 10n)` , which Lean understands mathematically as finding a "witness" value `c` such that  `n^2 + 10n = 5c` . The use tactic provides that exact witness. Lean now changes the goal to proving the equality:  `n^2 + 10n = 5(5k^2 + 10k)` .
- `rw[hk]`
    - The `rw` (rewrite) tactic looks at the equation in hypothesis `hk` `( n = 5k )` and replaces every instance of  `n`  in the goal with  `5k` . The goal updates to:  `(5k)^2 + 10(5k) = 5(5k^2 + 10k)` .
- `ring`
    - Expands, groups, and simplifies both sides of the equation algebraically. Since both sides simplify to  `25k^2 + 50k` , ring recognizes they are mathematically identical and closes the proof.

> [!Note]
> `m∣n` unfolds as `n = 5m` 
