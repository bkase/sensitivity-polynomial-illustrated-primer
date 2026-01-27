# Sensitivity Conjecture Illustrated Primer

An experiment in making formal mathematics accessible: an interactive walkthrough of the Sensitivity Conjecture proof, inspired by the Young Lady's Illustrated Primer from Neal Stephenson's *The Diamond Age*.

**[View the Illustrated Primer](https://bkase.github.io/sensitivity-polynomial-illustrated-primer/)**

## What is this?

This project combines:

1. **A Lean 4 formalization** of the Sensitivity Conjecture proof
2. **An interactive web primer** that walks through the proof step-by-step

The goal is to explore how we might make formal proofs more approachable by pairing machine-checked mathematics with guided explanations. This is an experiment that could potentially be applied to other formalized research.

## The Sensitivity Conjecture

The Sensitivity Conjecture was a 30-year-old open problem in theoretical computer science, finally resolved by Hao Huang in 2019 with an elegant 2-page proof.

The conjecture relates two measures of Boolean function complexity:
- **Sensitivity**: the maximum number of single-bit input changes that can flip the output
- **Degree**: the degree of the function's multilinear polynomial representation

Huang proved that for any Boolean function f of degree n:

```
sensitivity(f) >= sqrt(n)
```

The proof constructs a clever matrix (the "Huang matrix") on the hypercube graph and uses spectral methods to establish the bound.

## Repository Structure

- `sensitivity.lean` - The Lean 4 formalization of the proof
- `primer-app/` - Interactive web application (React + MDX)
- `docs/` - Built static site (deployed to GitHub Pages)

## Building

### Lean proof

```bash
lake build
```

This typechecks `sensitivity.lean` against Mathlib.

### Web application

```bash
cd primer-app
bun install
bun run build
```

The built output goes to `docs/` for GitHub Pages deployment.

## References

- Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." *Annals of Mathematics* 190.3 (2019): 949-955.
- [Mathlib's Archive/Sensitivity.lean](https://github.com/leanprover-community/mathlib4/blob/master/Archive/Sensitivity.lean) - An earlier Lean formalization in Mathlib
