# Finite Sum and Induction

<br/>

## Drill 6.1 (Sum of a Constant)

### `(n : ℕ) : ∑ k ∈ Finset.range n, (5 : ℝ) = 5 * n`

- The theorem asks to prove that summing the constant `5` exactly `n` times (which is what `Finset.range n` represents) equals `5 * n`.
- `simp` automatically recognizes the standard mathematical rule for summing a constant over a finite set, `∑ k ∈ Finset.range n, (5 : ℝ)` into simplified algebraic term `n * 5`.
- `ring` now simply solves `n * 5 = 5 * n`, closing goal.

<br/>

## Drill 6.2
### `(n: ℕ) (a : ℕ → ℝ) (h₀: (∑ k ∈ Finset.range n, a k) = 12) (h₁: a n = 7) : (∑ k ∈ Finset.range (n + 1), a k) = 19`

- The theorem asks to prove that if the sum of the first `n` terms is 12 and the `nth` term is 7, the total sum of the first `n + 1` terms is 19.
- `rw [Finset.sum_range_succ]` expands the summation limit, splitting `∑ k ∈ Finset.range (n + 1), a k` into the sum of the first `n` terms plus the final term: `(∑ k ∈ Finset.range n, a k) + a n = 19`.
- `linarith` automatically applies hypotheses `h₀` and `h₁` to evaluate `12 + 7 = 19`, closing the goal.

<br/>

## Drill 6.3
### `(a : ℕ → ℝ) (h: a 0 = 2 ∧ a 1 = 3 ∧ a 2 = 5) : ∑ k ∈ Finset.range 3, a k = 10`

- The theorem asks to prove that summing the first three terms of sequence `a` (from index 0 to 2) equals 10, given their specific values.
- `simp [Finset.sum_range_succ, h]` repeatedly unrolls the summation limit `Finset.range 3` into individual terms (`a 0 + a 1 + a 2`) and automatically substitutes their exact values from hypothesis `h`.
- `norm_num` resolves the remaining basic arithmetic `2 + 3 + 5 = 10`, closing the goal.

<br/>

## Drill 6.4 (Two Approaches)
### `(a : ℕ → ℝ) (n : ℕ): 0 ≤ ∑ k ∈ Finset.range n, (a k)^2`

- The theorem asks to prove that the sum of squared real numbers over any finite range is always greater than or equal to zero.
- Approach 1: `apply` and `exact`
    - `apply Finset.sum_nonneg` transforms the goal of proving the total sum is non-negative into a subgoal requiring every individual term in the sum to be non-negative.
    - `intro k hk` brings an arbitrary index `k` and the condition `hk` (that `k` is within the summation range) into the local context.
    - `exact sq_nonneg (a k)` closes the goal by applying the fundamental mathematical fact that any real number squared is non-negative.
- Approach 2: `positivity`
    - `positivity` is a specialized automation tactic for signs. It directly scans the expression, recognizes that real squares are always non-negative and that sums of non-negative numbers are non-negative, instantly closing the goal.

<br/>

## Drill 6.5
### `(a b : ℕ → ℝ) (n : ℕ) (h: ∀ k, a k ≤ b k) : ∑ k ∈ Finset.range n, a k ≤ ∑ k ∈ Finset.range n, b k`

- The theorem asks to prove that if every term in sequence `a` is less than or equal to the corresponding term in sequence `b`, the sum of the first `n` terms of `a` is less than or equal to the sum of `b`.
- `apply Finset.sum_le_sum` transforms the goal of comparing two sums into a subgoal requiring the inequality to hold for every individual term.
- `intro k hk` brings an arbitrary index `k` and its membership condition in the sum range (`hk`) into the local context.
- `exact h k` applies the universal hypothesis `h` specifically to `k`, proving `a k ≤ b k` and closing the goal.

<br/>

## Drill 6.6
### `(a : ℕ → ℝ) (n : ℕ) (h: ∀ k, a k ≤ 3): ∑ k ∈ Finset.range n, a k ≤ 3 * n`

- The theorem asks to prove that if every term in a sequence is less than or equal to 3, the sum of its first `n` terms is less than or equal to `3 * n`.
- `have h₀` establishes the intermediate sum inequality `∑ k ∈ Finset.range n, a k ≤ ∑ k ∈ Finset.range n, 3`. `apply Finset.sum_le_sum` reduces this to a term-by-term comparison, which is closed by `intro k hk` and `exact h k`.
- `simp at h₀` evaluates the summation of the constant on the right side, transforming the hypothesis `h₀` into `∑ k ∈ Finset.range n, a k ≤ n * 3`.
- `linarith` perfectly matches this simplified bound against the main goal, closing the proof.

<br/>

## Drill 6.7
### `(a : ℕ → ℝ) (n : ℕ) (h₀: n ≠ 0) (h₁ : ∀ k, a k < 2) : ∑ k ∈ Finset.range n, a k < 2 * n`

- The theorem asks to prove that if every term in a sequence is strictly less than 2, and the sum has at least one term (`n ≠ 0`), the total sum is strictly less than `2 * n`.
- `have h` establishes that the summation range is non-empty (`(Finset.range n).Nonempty`) by applying `Finset.nonempty_range_iff` to the non-zero hypothesis `h₀`.
- `have H` generates the strict sum inequality `∑ k ∈ Finset.range n, a k < ∑ k ∈ Finset.range n, 2` by feeding the non-empty proof `h` and the term-by-term strict inequality `h₁` into `Finset.sum_lt_sum_of_nonempty`.
- Think of `(fun k _ => h₁ k)` as a function taking two inputs to return one output:
    - `k` (Input 1): The specific index in the sum.
    - `_` (Input 2): The proof that `k` is inside the sum's range (ignored here because `h₁` applies to *all* numbers, not just those in the range).
    - `=> h₁ k` (Output): Plugs `k` into the general rule `h₁` to generate the exact proof Lean needs i.e. a(k) < 2 for that specific index.
- `simp at H` evaluates the summation of the constant on the right side, transforming `H` into `∑ k ∈ Finset.range n, a k < n * 2`.
- `linarith` perfectly matches this simplified strict bound against the main goal, closing the proof.
