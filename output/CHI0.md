# CHI0: Parity character chi_S

## Intuition and motivation

When you study a Boolean function f on the n-dimensional hypercube (all 0/1 strings of length n), you want a small set of "simple patterns" you can combine to build any function. The parity characters are those patterns. Each one is a checkerboard-like coloring of the cube: it alternates +1 and -1 depending on whether an even or odd number of selected bits are on. These patterns are the basic "waves" in the Fourier analysis of Boolean functions. They let us measure how much f aligns with a specific parity pattern, which later drives the degree and sensitivity arguments.

In this proof, CHI0 is the first step toward Fourier analysis and toward the parity-flip fact used in the sensitivity graph argument. Without chi_S, you cannot define Fourier coefficients, the degree of f, or the parity-twisted transform g that powers the main combinatorial step.

## What CHI0 is (plain-language definition)

Pick a subset S of the coordinates {1, 2, ..., n}. For any input x in {0,1}^n, define:

```
chi_S(x) = +1  if x has an even number of 1s inside S
chi_S(x) = -1  if x has an odd number of 1s inside S
```

Equivalently, if you treat x as the set of indices where x_i = 1, then:

```
chi_S(x) = (-1)^(|S ∩ x|)
```

So chi_S is a parity check on a chosen subset of bits. It ignores all other coordinates. That is why it is called a "parity character."

### Analogy

Imagine a row of light switches (the bits of x). Choose some of those switches (the set S). chi_S(x) lights green (+1) if an even number of chosen switches are ON, and red (-1) if an odd number are ON. Each different choice of S creates a different alternating pattern across the hypercube.

## How this appears in the repo

**LaTeX (sensitivity-polynomial.tex)** defines it as:

```
\chi_S(x) := (-1)^{x \cdot S}
```

Here, "x · S" means the parity (even/odd) of the number of indices in S where x_i = 1. It is the same as |S ∩ x| mod 2.

**Lean (sensitivity.lean)** formalizes the same idea:

```lean
def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  if (Finset.filter (fun i => x i) S).card % 2 = 0 then 1 else -1
```

Read this as: filter S to the indices where x is true, count them, and check whether the count is even. Even -> 1, odd -> -1.

## Where CHI0 sits in the proof DAG

From `history/breakdown.md`:

**What CHI0 represents**
- The single definition of parity characters chi_S.

**What CHI0 depends on**
- **BC0** (the Boolean cube): you need the universe of bitstrings x : Fin n -> Bool and the idea of indexing bits by a subset S.

**What depends on CHI0**
- **FOURIER0**: Fourier coefficients are defined as averages of f(x) * chi_S(x).
- **FOURIER_AVG**: restriction-averaging identity uses chi_S explicitly.
- **GVAL0**: the g-transform uses chi_univ to flip signs and extract a nonzero mean.
- **NEIGH_PARITY**: along a hypercube edge, chi_univ flips sign.

## Why chi_S matters for the surrounding ideas

### Fourier coefficient (neighboring concept: FOURIER0)

The Fourier coefficient of f at S is the correlation between f and chi_S:

```
f_hat(S) = E_x [ f(x) * chi_S(x) ].
```

If f tends to agree with the parity pattern for S, this coefficient is large. If f is "balanced" with respect to that pattern, the coefficient is near zero. The degree of f is then the largest size |S| where f_hat(S) is nonzero.

### Parity flip along an edge (neighboring concept: NEIGH_PARITY)

When two vertices x and y differ in exactly one bit, the parity of the total number of 1s flips. For S = "all coordinates" (Finset.univ), this implies:

```lean
lemma chi_univ_neighbor {n : ℕ} (x y : Fin n → Bool) (h_adj : (hypercube_graph n).Adj x y) :
  chi Finset.univ x = -chi Finset.univ y
```

This is the "checkerboard" property: adjacent vertices have opposite chi_univ values. It is essential later when we relate the transformed function g(x) to edge flips in f.

### The g-transform (neighboring concept: GVAL0)

The proof defines a new function

```
g(x) = f(x) * chi_univ(x)
```

This twists f by the global parity pattern. If the top Fourier coefficient (at S = all bits) is nonzero, then the average of g is nonzero. That imbalance creates a large level set, which eventually leads to the sensitivity lower bound. None of this works without the parity character.

## A tiny example (n = 3)

Let S = {1, 3}. Then chi_S(x) depends only on bits 1 and 3:

- x = 101 has two 1s in S -> even -> chi_S(x) = +1
- x = 100 has one 1 in S -> odd -> chi_S(x) = -1
- x = 011 has one 1 in S (bit 3 is 1, bit 1 is 0) -> chi_S(x) = -1

So chi_S slices the cube into alternating bands, based only on the parity of the selected bits.

## Self-contained takeaway

CHI0 defines the parity characters chi_S: the +1/-1 patterns that check even/odd parity on a chosen subset of coordinates. They are the building blocks for Fourier analysis on the Boolean cube and the key parity gadget used later in the proof. If you know what a bitstring is and what "even vs odd" means, you have everything needed to understand chi_S.
