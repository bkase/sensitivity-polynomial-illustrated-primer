# DEG0: Degree(f) from Fourier support

## Intuition and motivation

The proof uses Fourier analysis on the Boolean cube: every Boolean function f can be written as a sum of parity patterns (the chi_S functions). Each pattern is labeled by a subset S of the input bits. If S is large, that term mixes many bits together at once; if S is small, the term only depends on a few bits.

The **degree** of f is the size of the largest subset S that actually appears with a nonzero coefficient. This is a clean way to say "how high-order" the function is. The main theorem compares sensitivity to this degree, so we need a precise, formal definition that works both in the lecture notes and in Lean.

In the proof strategy, degree also lets us isolate a "top" Fourier term and either use it directly (the full-degree case) or restrict the function to a smaller cube so that this term becomes the top term there.

## What DEG0 is (plain-language definition)

Fourier analysis writes f as a sum of parity patterns:

```
f(x) = sum over S of f_hat(S) * chi_S(x)
```

The **Fourier support** is the set of all S where f_hat(S) is not zero. The degree is just the size of the largest S in that support:

```
deg(f) = max { |S| : f_hat(S) != 0 }
```

So degree measures the largest number of input bits that appear together in any nonzero Fourier term.

### Analogy

Think of each chi_S as a "frequency band" in an equalizer. Small sets S are low-frequency patterns (simple, broad structure). Large sets S are high-frequency patterns (fine, intricate structure). The degree is the highest frequency band that actually has nonzero energy.

## How this appears in the repo

**LaTeX (sensitivity-polynomial.tex)** sets up the idea in the Fourier section:

> "These chi are an orthogonal basis... This means every function can be expressed as a 'polynomial' and we can talk about the 'degree' of a function."

The explicit formal definition is in the Lean file.

**Lean (sensitivity.lean)** defines degree as the maximum size of any subset S with nonzero Fourier coefficient:

```lean
noncomputable def degree {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.sup (Finset.filter (fun S => fourier_coeff f S ≠ 0) Finset.univ) Finset.card
```

Read this as: take all subsets S of {1..n}, keep the ones where `fourier_coeff f S` is not zero, then take the maximum of `S.card`. `Finset.sup` is the "max" operator for a finite set.

## Where DEG0 sits in the proof DAG

From `history/breakdown.md`:

**What DEG0 represents**
- The single definition: degree(f) is the maximum |S| with nonzero Fourier coefficient.

**What DEG0 depends on**
- **FOURIER0**: you cannot talk about degree until Fourier coefficients are defined.

**What depends on DEG0**
- **FULLCOEF**: if degree(f) = n, then the top coefficient at S = univ is nonzero.
- **DEG_WITNESS**: there exists a set S with |S| = degree(f) and f_hat(S) != 0.
- **DEG_FROM_TOP**: if the top coefficient is nonzero, then the function has full degree.

## How DEG0 connects to neighboring concepts

### Fourier coefficients (FOURIER0)

Fourier coefficients tell you which parity patterns are present in f. Degree is a summary statistic of that list: it looks only at the largest set size among the nonzero coefficients.

### Full-degree witness (FULLCOEF)

In the special case degree(f) = n (all n bits appear together), the proof needs the top coefficient at S = univ to be nonzero. This is exactly what FULLCOEF establishes using DEG0.

### Degree witness set (DEG_WITNESS) and restriction (DEG_FROM_TOP)

For the general case, DEG0 guarantees there is some subset S of size k = degree(f) with a nonzero Fourier coefficient. The proof then restricts f to that subset so the restricted function has full degree k. This is the core reduction step from "general degree" to the full-degree case.

## Small example (intuition only)

If f depends only on the first bit (say, f(x) = x_1), then it can only correlate with parity patterns that mention bit 1. All larger subsets that do not include bit 1 are irrelevant. In this case, the largest nonzero Fourier term involves exactly one bit, so deg(f) = 1.

## Self-contained takeaway

DEG0 formalizes "degree" as the largest size of a subset of bits that shows up with a nonzero Fourier coefficient. It is the bridge between Fourier structure and the combinatorial arguments about sensitivity: it tells you how complex the function is in terms of high-order parity patterns and gives you a concrete subset to focus on in the reduction steps.
