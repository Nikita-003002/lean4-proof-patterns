# Lean 4 Proof Patterns

- A structured reference guide and practice repository for mastering mathematical proofs in Lean 4. This project breaks down the mechanical behaviors of common Lean tactics (like `linarith`, `ring`, `omega`, `zify`, and `linear_combination`) and maps out exactly how they interact with different mathematical structures.

## Repository Structure

- All proofs and reference notes are located in the `Drills/` directory, which is divided into eight conceptual sets.

    - **Individual Drills:** Each set contains 10 to 13 specific `.lean` files (e.g., `drill_1_1.lean`), demonstrating a specific theorem and the tactics required to close it.
    - **Detailed Notes:** Each `Set` folder contains its own `README.md` with deep dives into the mechanical behavior of the tactics used in those specific drills.
    - **CI/CD:** The repository includes a GitHub Actions workflow (`lean_action_ci.yml`) to automatically build and verify the proofs on push.

## Guide Overview

### Set 01: Non-Linear Bounding and Linarith

Focuses on the mechanics of `linarith` and how to feed it non-linear terms.

- **Core Concepts:** Handling squares (`x ^ 2`), products (`x * y`), and absolute values (`|x|`).
- **Key Tactics/Lemmas:** `sq_nonneg`, `abs_nonneg`, `ring` normalization, and `positivity` AST roll-ups.

- Focus: Feeding manual non-negative facts to linarith when it chokes on non-linear terms.

    - Drill 1.1 - 1.2: Single-variable squares (sq_nonneg).

    - Drill 1.3 - 1.4: Multi-variable squares, expansions.

    - Drill 1.5 - 1.7: Absolute values (abs_nonneg) and splitting ∧ sub-goals using constructor.

    - Drill 1.8: Unpacking bounded absolute values (|x| ≤ a) into linear systems.

    - Drill 1.9: Using nlinarith to automatically multiply pairwise non-negative terms.

    - Drill 1.10: Using positivity to build an AST and evaluate signs for strict inequalities.

### Set 02: Divisibility, Parity and Existentials

- Transitions from basic algebra to structural number theory by dismantling existential hypotheses ("there exists an integer such that...").

- **Core Concepts:** The 4-Step Existential Rhythm (`obtain` -> `use` -> `rw` -> `ring`) and the Witness Principle.
- **Key Tactics/Lemmas:** `use`, `obtain`, `Even`, `Odd`, and basic modular arithmetic.

- Focus: The 4-step existential rhythm (obtain -> use -> rw -> ring) for number theory.

    - Drill 2.1: Providing direct witnesses for raw ∃ equations.

    - Drill 2.2 - 2.4: Unpacking hidden existentials (divisibility ∣, Even, Odd) and proving them via polynomial expansion.

    - Drill 2.5 - 2.6: Handling multiple existentials and transitivity logic.

    - Drill 2.7: Direct divisibility witnesses for sums.

    - Drill 2.8 - 2.9: Parity transformations and algebraic grouping (Odd and Even).

    - Drill 2.10: Resolving non-linear % (modulo) operations implicitly using omega.

### Set 03: Case Splitting (`|x|`, `min`, `max` and Parity)

- Navigating piecewise functions and logical disjunctions (`Either/Or`) that cause standard linear solvers to get stuck.

- **Core Concepts:** Splitting proofs into logical branches based on signs or structural disjunctions.
- **Key Tactics/Lemmas:** `rcases`, `le_total`, `abs_of_nonneg`, `max_eq_right`, and the `<;>` combinator.

- Focus: Managing piecewise functions and logical disjunctions (Either/Or).

    - Drill 3.1 - 3.2: Translating absolute inequalities (abs_le, abs_lt) into linear bounds.

    - Drill 3.3: Branching logic on disjunctions (∨) using rcases.

    - Drill 3.4 - 3.5: Using le_total to split proofs on 0 ≤ x and x ≤ 0 for abs_of_nonneg / abs_of_nonpos.

    - Drill 3.6: Applying <;> to generate multi-case matrices for nested absolute values.

    - Drill 3.7 - 3.8: Simplifying max a b and min a b.

    - Drill 3.9: Branching via the Zero Product Property (mul_eq_zero).

    - Drill 3.10: Structural disjunctions (Int.even_or_odd).

### Set 04: Type Casting and N <-> Z <-> R Bridges

- Managing Lean 4's strict separation of Natural numbers (`ℕ`), Integers (`ℤ`), and Reals (`ℝ`), and avoiding truncation traps (like `3 - 5 = 0` in `ℕ`).

- **Core Concepts:** Pushing and pulling variables across type boundaries to unlock algebraic tactics.
- **Key Tactics:** `zify`, `exact_mod_cast`, `push_cast`, and using `omega` for pure `ℕ`/`ℤ` arithmetic.

- Focus: Escaping truncation traps in ℕ (where 3 - 5 = 0) by pushing and pulling types.

    - Drill 4.1: Using omega to resolve systems of constraints over natural numbers.

    - Drill 4.2 - 4.3: Using zify to cast natural number subtraction safely into ℤ.

    - Drill 4.4 - 4.6: Using exact_mod_cast to strip ℝ coercions back down to ℕ.

    - Drill 4.7 - 4.8: Using push_cast to force outward coercions inward so ring and linarith can execute.

    - Drill 4.9: Using omega to prove sub-goals before type-correcting the main goal.

    - Drill 4.10: Combining nlinarith preprocessing with type-casting contradiction bounds.

### Set 05: Calc And Linear Combination

- Solving pure algebraic equalities (`=`) in generic Commutative Rings (`CommRing`) or Complex Numbers (`ℂ`) where inequality-based solvers (`linarith`) are mathematically invalid.

- **Core Concepts:** Transitive equality chains and polynomial zero-sum expansions.
- **Key Tactics:** `calc` blocks, `linear_combination`, and `ring`.

- Focus: Proving pure algebraic equalities (=) in generic Rings or ℂ where </≤ are invalid.

    - Drill 5.1 - 5.3: Direct comparison of the 3 core approaches (linear_combination, rw/show, and calc) across CommRing, ℂ, and ℝ.

    - Drill 5.4: linear_combination vs algebraic substitution using linarith + ring.

    - Drill 5.5: Polynomial factoring via exact polynomial multipliers.

    - Drill 5.6: Zero-product property on higher-degree polynomials.

    - Drill 5.7: Bypassing massive multipliers by structuring algebraic breakdowns in a calc block.

    - Drill 5.8: Injecting intermediate calc bounds into linarith to close main inequalities.

### Set 06: Finite Sum and Induction

- Handling sequences, finite sets (`Finset.range`), and proving properties across infinite discrete domains.

- **Core Concepts:** Unrolling sums term-by-term and the standard inductive rhythm (Base Case + Inductive Step).
- **Key Tactics/Lemmas:** `induction' n`, `Finset.sum_range_succ`, `apply Finset.sum_nonneg`, and `apply Finset.sum_le_sum`.

- Focus: Manipulating Finset bounds and structuring inductive proofs.

    - Drill 6.1: Summing constants.

    - Drill 6.2 - 6.3: Unrolling sums term-by-term using Finset.sum_range_succ and simp.

    - Drill 6.4: Proving sum non-negativity term-by-term (Finset.sum_nonneg and positivity).

    - Drill 6.5 - 6.7: Comparing two sums term-by-term (Finset.sum_le_sum).

    - Drill 6.8: Basic inductive rhythm (induction' n with d hd).

    - Drill 6.9: Complex induction requiring a helper lemma and zify to dodge subtraction limits.

    - Drill 6.10: Exponential inductive steps balanced inside a calc block.

### Set 07: Quantifiers (∀), Functions & Contradiction

- Working with universal rules, abstract functions (`f : ℝ → ℝ`), and proving by refutation.

- **Core Concepts:** Instantiating universal quantifiers with concrete values (`0`, `1`, `x`, `-x`) to generate usable equations.
- **Key Tactics:** `intro`, `by_contra`, `push Not`, and evaluating internal arithmetic with `norm_num`.

- Focus: Instantiating universal rules and isolating variables via refutation.

    - Drill 7.1 - 7.2: Supplying concrete inputs (0, 1) to universal rules (∀ x) to generate usable equations.

    - Drill 7.3: Applying rules to arbitrary inputs (x, -x).

    - Drill 7.4 - 7.6: Using norm_num to evaluate internal function arguments so linarith recognizes matching variables.

    - Drill 7.7: Evaluating recursive alternating sequences.

    - Drill 7.8: Setting up basic refutation (by_contra).

    - Drill 7.9: Simplifying complex negated logic with De Morgan's laws (by_contra!).

    - Drill 7.10: Pushing negations inward (push Not) to extract existential witnesses.

### Set 08: Denominators, Roots

- Managing fractions and square roots by explicitly proving non-zero and non-negative prerequisites.

- **Core Concepts:** Clearing denominators safely across inequalities and unwrapping squared roots.
- **Key Tactics/Lemmas:** `field_simp`, `field`, `Real.sq_sqrt`, `div_le_iff_of_neg`, and `div_lt_iff_of_neg`.

- Focus: Managing prerequisites for clearing fractions and evaluating square roots.

    - Drill 8.1 - 8.2: Flattening fractions algebraically (field_simp, field).

    - Drill 8.3 - 8.4: Manually providing non-zero proofs to mathematically justify fraction clearing.

    - Drill 8.5 - 8.7: Clearing strictly positive denominators in inequalities without flipping directions.

    - Drill 8.8 - 8.9: Providing non-negativity prerequisites for Real.sq_sqrt.

    - Drill 8.10: Combining root simplifications with linarith contradiction bounds.

    - Drill 8.11 - 8.12: Safely clearing negative denominators and flipping inequality directions.

    - Drill 8.13: Resolving mathematical equivalences (↔) for fractional operations.

## Usage

To build the project and verify all proofs locally:

```bash
lake build

```
