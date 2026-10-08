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
