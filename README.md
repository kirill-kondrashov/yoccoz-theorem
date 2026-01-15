# Machine-Generated Formalization of Yoccoz's Theorem

This repository contains a **machine-generated formal proof** of Yoccoz's Theorem for quadratic polynomials in Lean 4. This theorem is a key component of the Mandelbrot Local Connectivity (MLC) Conjecture, establishing it for non-renormalizable parameters.

Essentially, this is software that can help with moving forward with an exact proof **together** with human verification (if it allows formalizing with Lean).

This is a work in progress; there will be an update when (or if ☺ ) the proof is fully verified. This repository is shared at an early stage to simplify collaboration (not everyone has a github account).

The benefit of using Lean is that it is verified by the Lean kernel, even when it is generated. Some essential parts, such as definitions, useful lemmas, and theorems from the references, are included here. To have a closed loop, a few theorems (see below) are stated as axioms.

[Read the Documentation (PDF)](docs/proof.pdf), it includes Lean listings next to comments, and attempts to make the proofs human-readable.

## Disclaimer

> **This is an AI-assisted attempt to formalize modern mathematics.**
>
> The code and documentation in this repository were produced by a combination of actions of AI assistant and manual fixes. While the definitions and logical structure are checked by the Lean 4 kernel, the choice of axioms and the mathematical fidelity of the formalization to the standard literature should be verified by human experts.

## Axioms

Some of the statements used in the proof are stated as `axiom`s (keyword in Lean). They include:

### 1. Yoccoz Puzzles & Geometry
*   [`groetzsch_inequality`](Mlc/Quadratic/Complex/Groetzsch.lean#L64): Grötzsch's Inequality (Superadditivity of modulus).
    *   Source: [Milnor, Dynamics in One Complex Variable, Corollary B.5] (Local: `refs/9201272v1.pdf`)
    *   Note: This axiom is used to prove `modulus_summable_of_nontrivial_intersection`, which states that if the intersection of nested pieces is non-trivial, the sum of moduli converges.
*   **Basic Properties**:
    *   [`modulus_nonneg_ax`](Mlc/Quadratic/Complex/Groetzsch.lean#L50): Modulus is non-negative.
        *   Source: [Milnor, Dynamics in One Complex Variable] (Local: `refs/9201272v1.pdf`, Appendix B)

## Verification

To verify the proof and check for axioms (`sorry` keyword in Lean), run:

```bash
make check
```

This will output any axioms used in the proof.

Output:
```
✅ The proof of 'MLC.yoccoz_theorem' is free of 'sorry'.
All axioms used:
- propext
- Quot.sound
- Classical.choice
- MLC.Quadratic.groetzsch_inequality
- MLC.Quadratic.modulus_nonneg_ax
```
