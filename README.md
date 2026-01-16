# Machine-Generated Formalization of Yoccoz's Theorem

[![build](https://github.com/kirill-kondrashov/yoccos-theorem/actions/workflows/badge.svg)](https://github.com/kirill-kondrashov/yoccos-theorem/actions/workflows/lean_action_ci.yml)

This repository contains a **machine-generated formal proof** of Yoccoz's Theorem for quadratic polynomials in Lean 4. This theorem is a key component of the Mandelbrot Local Connectivity (MLC) Conjecture, establishing it for non-renormalizable parameters.

Essentially, this software facilitates progress toward an exact proof **in collaboration** with human verification, leveraging the rigor of formalization in Lean.

> [!NOTE]
> This is a work in progress. Updates will be posted when (or if ☺) the proof is fully verified. This repository is shared at an early stage to simplify collaboration.

The primary benefit of using Lean is that the logic is verified by the Lean kernel, ensuring correctness relative to the definitions and axioms provided. Some essential parts, such as definitions, useful lemmas, and theorems from the literature, are included. All domain-specific results are now formalized, relying only on Lean's standard axioms.

[**Read the Documentation (PDF)**](docs/proof.pdf): Includes Lean listings alongside comments, attempting to make the proofs human-readable.

## Disclaimer

> [!NOTE]
> **This is an AI-assisted attempt to formalize modern mathematics.**
>
> The code and documentation in this repository were produced by a combination of AI assistance and manual refinement. While the definitions and logical structure are checked by the Lean 4 kernel, the choice of axioms and the mathematical fidelity of the formalization to the standard literature require expert verification.

## Verification

To verify the proof and check for any remaining gaps (the `sorry` keyword in Lean), run:

```bash
make check
```

This will analyze the codebase and output any axioms or unproven statements used.

**Expected Output:**
```
✅ The proof of 'MLC.yoccoz_theorem' is free of 'sorry'.
All axioms used:
- propext
- Quot.sound
- Classical.choice
```
