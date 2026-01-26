# BC0: The Boolean cube and how we enumerate it

## Intuition and motivation

Before the proof can talk about sensitivity, Fourier coefficients, or graphs, it needs a universe of inputs to talk about. BC0 is that foundation. It says: our inputs are all n-bit strings, and we can list them all so we can count things and take averages. That is the Boolean hypercube. Without this, later definitions like "average of f(x) over all x" or "neighbors that differ in one bit" are not even well-formed.

Think of a function f as a truth table: each row is one assignment of n switches (on/off). BC0 is the decision to make that table precise and finite, so we can say things like "sum over all rows" or "pick the worst row."

## The idea in plain language

- **Vertices of the hypercube**: An input x is just a choice of 0/1 for each of n positions. There are 2^n such choices. If you draw these choices as corners of an n-dimensional cube, each choice is a vertex.
- **Enumeration**: Because there are finitely many vertices, we can *enumerate* them. In Lean, that enumeration is represented by `Finset.univ`, the finite set of all elements of a finite type. Here the finite type is "functions from `Fin n` to `Bool`," i.e., all n-bit strings.
- **Why enumeration matters**: Many later definitions are "averages" or "counts." An average is just "sum over all vertices divided by 2^n." A count is "how many vertices satisfy a property."

Analogy: if the hypercube is a giant checklist of all possible switch settings, `Finset.univ` is "the entire checklist." Summing over `Finset.univ` is like adding up a column of the checklist.

## How BC0 appears in the repo

### LaTeX (lecture notes)

The notes introduce Boolean functions as maps from all bitstrings:

```tex
A function f : 2^n -> 2 is called a boolean function.
```

Here `2^n` means the set of all n-bit strings. This is the same "vertex set of the hypercube."

### Lean (formalization)

In Lean, an n-bit string is a function `x : Fin n -> Bool`. The set of all such x is finite, so Lean provides `Finset.univ` as the enumeration of all of them.

You can see this in the Fourier coefficient definition:

```lean
noncomputable def fourier_coeff {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℝ :=
  (Finset.sum Finset.univ (fun x => (if f x then 1 else 0) * chi S x)) / 2^n
```

The parity character `chi` is also defined on the Boolean cube:

```lean
def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  if (Finset.filter (fun i => x i) S).card % 2 = 0 then 1 else -1
```

Explanation:
- `Finset.sum Finset.univ ...` means "sum over all vertices x of the cube."
- Dividing by `2^n` turns that sum into an average (there are exactly 2^n vertices).

The sensitivity definition uses the same universe:

```lean
def sensitivity {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.sup Finset.univ (fun x => Finset.card (Finset.filter (fun y => (Finset.card (Finset.filter (fun i => x i ≠ y i) Finset.univ) = 1) ∧ f x ≠ f y) Finset.univ))
```

That `Finset.sup Finset.univ` is "take the maximum over all vertices x."

So BC0 is not a theorem; it is the *ground level* that makes "sum over all x" and "max over all x" meaningful in both the notes and the Lean code.

## Dependencies and downstream uses (from breakdown.md)

**What BC0 represents**
- The universe of inputs: the Boolean cube, represented as functions `x : Fin n -> Bool`.
- The ability to **enumerate all vertices** (and all coordinate positions) using `Finset.univ`, so sums and averages are well-defined.

**What BC0 depends on**
- Nothing in the proof graph. It is a base concept that assumes only the idea of "n-bit strings" and "finite enumeration."

**What depends on BC0**
BC0 is a prerequisite for:
- **BC1 (neighbor relation / hypercube graph)**: adjacency is defined by comparing two vertices in the same universe.
- **BC3 (reindexing to Fin (2^n))**: reindexing only makes sense once the vertex set is fixed.
- **SEN0 (sensitivity)**: defined as a maximum over all vertices.
- **CHI0 (parity character chi_S)**: defined on vertices x.
- **FOURIER0 (Fourier coefficients)**: sums over all vertices.
- **RESTRICT0 (restriction)**: still a function on a smaller Boolean cube; built from the same notion of vertex.
- **GVAL0 (g-transform)**: uses sums over all vertices of the cube.

You can think of BC0 as the "shared coordinate system" for all these later objects.

## Connections to neighboring concepts

- **BC1 (neighbors)**: Once you have vertices, you can define edges by "differ in exactly one coordinate." That coordinate counting is another use of enumeration: you count how many positions i differ between x and y.
- **CHI0 and FOURIER0**: The parity character `chi_S(x)` and the Fourier coefficient of f are *functions on vertices* and *averages over vertices*. Both are meaningless without a finite, enumerable set of x.
- **SEN0**: Sensitivity is a max over all x and counts neighbors around each x. BC0 supplies the universe over which both the max and the counts are taken.

## Tiny example (n = 2)

With two bits, the hypercube has 4 vertices:

```
00, 01, 10, 11
```

`Finset.univ` is the formal version of "the set {00,01,10,11}."

If you wanted the average value of f across all vertices, you would compute:

```
(f(00) + f(01) + f(10) + f(11)) / 4
```

That is exactly what the Lean `fourier_coeff` definition does, but generalized to n bits.

## Takeaway

BC0 is the proof's foundation: it sets the domain of all inputs and provides a way to enumerate them. Every later definition that says "for all x" or "average over x" is leaning on BC0. Once you accept "the Boolean cube is the set of all n-bit strings, and we can list all of them," the rest of the proof has a concrete playground to work in.
