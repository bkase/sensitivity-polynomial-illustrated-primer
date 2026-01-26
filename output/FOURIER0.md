# FOURIER0: Fourier coefficient f_hat(S)

## Intuition and motivation

Fourier analysis on the Boolean cube is a way to break a Boolean function into simple, repeating parity patterns. Each pattern is a "checkerboard" that flips sign depending on the parity of a chosen set of bits (the chi_S functions from CHI0). The Fourier coefficient f_hat(S) is the number that tells you how much of that pattern is present in your function.

In this proof, we need Fourier coefficients for two reasons:
1) The degree of f is defined by which Fourier coefficients are nonzero.
2) Later steps average and transport these coefficients across restrictions of f. Without a precise definition of f_hat(S), those steps have nothing to talk about.

So FOURIER0 is the gateway from "a Boolean function on the cube" to "a function with a Fourier spectrum we can measure."

## What FOURIER0 is (plain-language definition)

You have:
- A Boolean function f : {0,1}^n -> {0,1}
- A subset S of the coordinate positions {1, ..., n}
- The parity character chi_S(x), which is +1 for even parity on S and -1 for odd parity

The Fourier coefficient f_hat(S) is the average of f(x) * chi_S(x) over all inputs x:

```
f_hat(S) = (1 / 2^n) * sum_{x in {0,1}^n} f(x) * chi_S(x)
```

Interpretation:
- If f tends to be 1 when chi_S(x) = +1 and 0 when chi_S(x) = -1, the coefficient is positive.
- If f tends to be 1 when chi_S(x) = -1, the coefficient is negative.
- If f does not care about that parity pattern, the coefficient is near zero.

Think of it as a correlation score between f and the parity pattern chi_S.

### Analogy

Imagine a mixing board where each parity pattern is a tone. The Fourier coefficient is the volume knob for that tone. If the knob is 0, that tone is absent. If it is large, the tone strongly appears in the function.

## How this appears in the repo

**LaTeX (sensitivity-polynomial.tex)**: The "Fourier analysis" section defines chi_S and says these chi_S functions form an orthogonal basis for Boolean functions. The Fourier coefficient is the inner product with chi_S, which is exactly the average shown above.

**Lean (sensitivity.lean)** defines the coefficient directly as an average. Here is the key definition (verbatim from sensitivity.lean):

```lean
noncomputable def fourier_coeff {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℝ :=
  (Finset.sum Finset.univ (fun x => (if f x then 1 else 0) * chi S x)) / 2^n
```

This matches the formula above: it converts f(x) to 0 or 1 via `if f x then 1 else 0`, multiplies by `chi S x`, sums over all x in `Finset.univ`, and divides by 2^n to get the average.

## Where FOURIER0 sits in the proof DAG (from history/breakdown.md)

**What FOURIER0 represents**
- The single definition of the Fourier coefficient f_hat(S), i.e., "how much f correlates with chi_S."

**What FOURIER0 depends on**
- **BC0**: the Boolean cube and the ability to sum/average over all x.
- **CHI0**: the parity characters chi_S that define the patterns you correlate against.

**What depends on FOURIER0**
- **DEG0**: degree is defined as the largest |S| with f_hat(S) != 0.
- **FOURIER_AVG**: the restriction-averaging identity expresses f_hat(S) as an average of top coefficients of restrictions.
- **DEG_FROM_TOP**: if the top coefficient at univ is nonzero, the function has full degree.

## Connections to neighboring concepts

### CHI0 -> FOURIER0
CHI0 gives the parity patterns chi_S. FOURIER0 measures how much f aligns with each pattern. No chi_S, no Fourier coefficients.

### FOURIER0 -> DEG0
DEG0 defines the degree of f as the largest size of a set S with f_hat(S) != 0. So the degree is just "the highest-order nonzero Fourier coefficient."

### FOURIER0 -> FOURIER_AVG -> DEG_FROM_TOP
The restriction-averaging lemma says that f_hat(S) equals the average of the top coefficients of restrictions of f. If that average is nonzero, at least one restriction has a nonzero top coefficient, and DEG_FROM_TOP then tells you that restricted function has full degree. This is the core of the reduction step in the proof.

## A tiny example (n = 2)

Let f(x) = 1 if the first bit is 0, and 0 otherwise. Let S = {1}. Then chi_S(x) = +1 when the first bit is 0 and -1 when it is 1.

Over the four inputs:
- Two inputs have first bit 0: f = 1, chi_S = +1
- Two inputs have first bit 1: f = 0, chi_S = -1

So the sum of f(x) * chi_S(x) is 2, and:

```
f_hat(S) = 2 / 2^2 = 1/2
```

That positive coefficient says: "f lights up exactly on the +1 side of the chi_S checkerboard."

## Self-contained takeaway

FOURIER0 defines f_hat(S): the average correlation between f and a parity pattern chi_S. It is the basic numerical handle that lets the proof talk about degree, about restrictions, and ultimately about why full degree forces sensitivity to be large.
