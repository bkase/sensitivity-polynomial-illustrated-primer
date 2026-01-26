# SUBMAT: principal submatrix A_n_fin[S]

## Intuition and motivation
In this proof, we often take a big object (the whole hypercube graph and its Huang matrix) and then zoom in on a subset of vertices S, because S is where the action is (a level set of g that is larger than half the cube). To "zoom in" on a matrix, you do not keep all rows and columns. You keep only the rows and columns indexed by S. That cropped matrix is the principal submatrix. This is the exact object that lets us compare:
- the matrix side (Huang's matrix A_n_fin), and
- the graph side (the induced subgraph on S),
while still preserving symmetry and enabling spectral tools like interlacing.

Think of a matrix as a big spreadsheet of how every vertex interacts with every other vertex. Taking a principal submatrix is like selecting the same subset of rows and columns, so you only see interactions inside the chosen group.

## Plain-language definition
Let A be a matrix whose rows and columns are labeled by vertices of a graph. For a subset S of vertices, the principal submatrix A[S] is the smaller matrix whose rows and columns are only those in S:

```
A[S] = (A_ij) for i in S, j in S
```

It is "principal" because you restrict both rows and columns to the same subset. This keeps symmetry: if A is symmetric, then A[S] is symmetric too.

Analogy: You have a social network adjacency table. You want to study just the people in S. The principal submatrix is the table of who in S is connected to who in S.

## Where SUBMAT sits in the proof graph
From `history/breakdown.md`, the SUBMAT atom is:
- "take principal submatrix A_n_fin[S]"

Dependencies (what SUBMAT needs first):
- **HUANG_REIDX**: the Huang matrix A_n is reindexed to Fin(2^n) so its rows/columns line up with hypercube vertices. Only then does "subset S of vertices" make sense for the matrix.

What depends on SUBMAT:
- **SUBMAT_BOUND**: compares entries of A_n_fin[S] to adjacency of the induced graph on S.
- **RAYLEIGH** (and downstream **INTERLACE**): uses the principal submatrix when comparing eigenvalues via Rayleigh quotient and interlacing.

## Concrete snippets from the Lean file
In `sensitivity.lean`, the principal submatrix is defined exactly as "restrict A to the indices in S":

```lean
/-
Definition of a principal submatrix.
-/
def principal_submatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Matrix S S ℝ :=
  A.submatrix Subtype.val Subtype.val
```

Because Lean wants matrices indexed by a type like `Fin k` (numbers 0..k-1), there is also a reindexed version that turns the subset S into `Fin (card S)`:

```lean
/-
Reindexed principal submatrix to Fin (card S).
-/
def principal_submatrix_fin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
  Matrix (Fin (Fintype.card {x // x ∈ S})) (Fin (Fintype.card {x // x ∈ S})) ℝ :=
  Matrix.reindex (Fintype.equivFin {x // x ∈ S}) (Fintype.equivFin {x // x ∈ S}) (principal_submatrix A S)
```

Plain-English translation:
- `principal_submatrix` says: keep only rows/columns in S.
- `principal_submatrix_fin` says: after we keep only S, relabel those rows/columns as 0..|S|-1 so we can use standard matrix tools.

## Connection to neighboring concepts
SUBMAT connects the Huang matrix to the induced subgraph on S:
- The induced subgraph on S is built separately (atom **IND_GRAPH**).
- SUBMAT gives the matrix A_n_fin[S] for the same subset S.
- Then **SUBMAT_BOUND** compares these two: the absolute values of entries in A_n_fin[S] are bounded by the adjacency indicator of the induced graph. This is the bridge needed to convert matrix eigenvalue bounds into graph degree bounds.

In the LaTeX notes (`sensitivity-polynomial.tex`), this shows up when the adjacency matrix of the induced subgraph (called H1) is turned into a submatrix of A_n (called H2). That "turning into a submatrix" is exactly the SUBMAT step.

## Why this matters later
Once you have A_n_fin[S]:
- You can bound its eigenvalues from above using graph degrees (via **SUBMAT_BOUND** and **SPEC_UPPER**).
- You can bound its eigenvalues from below by interlacing with the full A_n_fin (via **RAYLEIGH** and **INTERLACE**).
Those two bounds squeeze and produce the key inequality leading to sensitivity >= sqrt(deg).

## Prerequisites to keep in mind
To fully follow SUBMAT, it helps to know:
- A matrix can represent a graph's adjacency.
- A principal submatrix is a row/column restriction to a subset.
- Reindexing just relabels rows/columns without changing values.

With those in place, SUBMAT is the clean "zoom in on S" operation that makes the later spectral arguments possible.
