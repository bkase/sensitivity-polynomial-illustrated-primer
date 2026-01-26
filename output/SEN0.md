# SEN0: Sensitivity definition

## Intuition and motivation
Sensitivity is a way to measure how "fragile" a Boolean function is when you flip just one input bit. If a tiny change often flips the output, the function is sensitive. In this proof, sensitivity is the quantity we want to lower bound in terms of polynomial degree. So we need a precise definition that:
- looks only at one-bit changes (local behavior), and
- takes the worst case over all inputs (global behavior).

Think of a light panel with n switches. The function f tells you whether a light is on or off. Sensitivity asks: at which panel setting can you change the light by flipping as few single switches as possible? It counts, at that setting, how many single switches would flip the light. Then it picks the worst setting (the maximum).

## Plain-language definition
Inputs are n-bit strings. Two inputs are neighbors if they differ in exactly one bit. The sensitivity at input x is the number of neighbors y of x that make the output change:

```
local_sensitivity(f, x) = number of neighbors y of x with f(x) != f(y)
```

The (global) sensitivity is the maximum local sensitivity over all inputs:

```
s(f) = max over all x of local_sensitivity(f, x)
```

This is exactly the idea in the lecture notes:

```
Given x ~ y meaning "differ in one bit":
s(f) = max_x |{ y : x ~ y and f(x) != f(y) }|
```

## Graph/hypercube picture
The n-bit inputs form the vertices of the n-dimensional hypercube Q_n. An edge connects two vertices that differ in exactly one bit. Then:
- local sensitivity at x = number of edges from x that cross from f=0 to f=1
- global sensitivity s(f) = maximum such count over all vertices

So sensitivity is just "max edge boundary degree" for the cut defined by f.

## How SEN0 is encoded in Lean (ASCII rendering)
In `sensitivity.lean`, sensitivity is defined by filtering all inputs y that differ from x in exactly one coordinate, and also flip the output. (Here "card" counts elements.)

```lean
def sensitivity {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.sup Finset.univ (fun x => Finset.card (Finset.filter (fun y => (Finset.card (Finset.filter (fun i => x i ≠ y i) Finset.univ) = 1) ∧ f x ≠ f y) Finset.univ))
```

Read it as: for each x, count all y at Hamming distance 1 with f(x) != f(y), then take the maximum.

## Dependencies and what depends on SEN0
From `history/breakdown.md`:
- Depends on:
  - BC0: the Boolean cube as the universe of inputs, so we can quantify over all x and y
  - BC1: the neighbor relation / hypercube graph (Hamming distance 1)
- Used by:
  - SENS_MONO: "sensitivity does not increase under restriction" (restricting to a subcube can only remove neighbors)
  - DEG_SENS_LEVEL: "sensitivity equals degrees in a large induced subgraph" (used to bridge to the spectral argument)

## How it connects to neighboring concepts in the proof
The proof later builds a set S of inputs (a level set of a transformed function g) with many vertices. In that step, the key move is:
- For a vertex x in that level set, the number of neighbors inside S equals the number of neighbors where f flips.
- Therefore, the degree of x in the induced subgraph on S is exactly the local sensitivity at x.
- Taking the max degree in that induced subgraph gives a direct lower bound on s(f).

This is the bridge from combinatorics (counting edges in the hypercube) to the spectral part (bounding degrees via eigenvalues).

## Quick example
Let f(x) be parity (xor of all n bits). Flipping any one bit changes parity, so every input has local sensitivity n. Therefore s(f) = n.

Let f(x) be the first bit x1. Only flipping the first bit changes the value, so local sensitivity is always 1, and s(f) = 1.

These examples show how sensitivity measures "single-bit instability" and why the max over x matters.
