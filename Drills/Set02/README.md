# Divisibility, Parity and Existentials
This is where we transition from basic algebraic manipulation into structural mathematical reasoning. In number theory, almost everything — `divisibility`, `even numbers`, `odd numbers` — is secretly an existential statement ("there exists an integer such that...").

Learning from this Set:
- The 4-Step Existential Rhythm: How to mechanically dismantle existential hypotheses and construct proofs using the `obtain` -> `rw` -> `use` -> `ring` pipeline.
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

- `obtain ⟨k, hk⟩ := h₀` and `obtain ⟨m, hm⟩ := h₁` unpack the hypotheses, introducing specific variables `k` and `m` alongside their exact equations `a = 4 * k + 1` and `b = 4 * m + 3`.
- For `∃`, the `use` tactic provides a witness.
- Here `k + m + 1` is the witness. The goal changes to `a + b = 4 * (k + m + 1)`.
- `rw [hk, hm]` substitutes the variables using the extracted equalities, transforming the goal into `(4 * k + 1) + (4 * m + 3) = 4 * (k + m + 1)`.
- `ring` evaluates both sides of the polynomial equation and closes the goal automatically.

> [!Note]
> The `ring` tactic is provided by Mathlib specifically for commutative rings (like integers). It automatically handles associativity, commutativity, and distributivity so we don't have to manually factor or rearrange the terms.
