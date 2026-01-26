# HUANG_REIDX: Reindexing the Huang matrix to Fin(2^n)

## Intuition and motivation

In the proof, the Huang matrix A_n is built with rows and columns indexed by bitstrings of length n (formally, functions `Fin n -> Bool`). But the later graph arguments talk about subsets of vertices and induced subgraphs where vertices are indexed as `Fin(2^n)` (the numbers 0..2^n-1). To compare a matrix entry with a graph edge on the same vertex labels, we need both objects to use the same indexing scheme.

HUANG_REIDX is the step that simply relabels A_n so its rows/columns are indexed by `Fin(2^n)` instead of by bitstrings. Nothing about the matrix changes numerically; only the names of the row/column labels do. This lets us line up the Huang matrix with the induced hypercube graph on a subset of vertices.

Analogy: imagine a city map where intersections are labeled by GPS coordinates (bitstrings), but the transit authority numbers intersections from 0 to N-1. The roads have not changed, just the labels. Reindexing is the official renaming step so you can compare your map to their bus schedule.

## What HUANG_REIDX represents

It is a transport step:
- Take the matrix A_n defined on the index type `(Fin n -> Bool)`.
- Use a bijection between those bitstrings and the numbers `0..2^n-1`.
- Apply that bijection to rename the rows and columns.

In Lean, the key definitions are:

```lean
/-
Equivalence between boolean functions and Fin (2^n).
-/
def boolFunEquivFin (n : ℕ) : (Fin n → Bool) ≃ Fin (2^n) :=
  (Fintype.equivFin (Fin n → Bool)).trans (finCongr (by
  norm_num [ Fintype.card_pi ]))

/-
Reindexing of Huang matrix to Fin (2^n).
-/
noncomputable def huang_matrix_fin (n : ℕ) : Matrix (Fin (2^n)) (Fin (2^n)) ℝ :=
  Matrix.reindex (boolFunEquivFin n) (boolFunEquivFin n) (huang_matrix n)
```

Interpretation: `Matrix.reindex` says

```
A_n_fin[i,j] = A_n[ (boolFunEquivFin n).symm i, (boolFunEquivFin n).symm j ]
```

So the numeric entry is the same, but the labels are now in `Fin(2^n)`.

## Why it matters in the proof

The proof compares:
- the reindexed Huang matrix `A_n_fin`, and
- the adjacency matrix of the induced hypercube graph on a subset S.

That comparison only makes sense if both are indexed by the same vertex set. Once A_n is reindexed, we can take principal submatrices on subsets of `Fin(2^n)` and compare entries directly to the induced graph adjacency indicator.

This is exactly what the later step uses:

```lean
/-- Absolute values of reindexed A_n match adjacency in the reindexed hypercube. -/
lemma abs_huang_fin_eq_adjacency_fin {n : Nat} (i j : Fin (2^n)) :
  |huang_matrix_fin n i j| = if (hypercube_graph_fin n).Adj i j then 1 else 0 := by
  ...
```

Without HUANG_REIDX, the indices would not align, and this entrywise comparison would be awkward or impossible.

## Connections to neighboring atoms

Dependencies (what HUANG_REIDX needs):
- BC3: the equivalence between `(Fin n -> Bool)` and `Fin(2^n)` and the general idea that reindexing preserves structure.
- HUANG_DEF: definition of A_n as the recursive block matrix.
- HUANG_PROP: the properties of A_n (symmetry, A_n^2 = nI, trace 0) that are transported to the reindexed version.
- ABS_ADJ: the fact that `|A_n|` matches hypercube adjacency on the original indexing.

Downstream uses (what depends on HUANG_REIDX):
- SUBMAT: take principal submatrices `A_n_fin[S]` for subsets `S` of `Fin(2^n)`.
- SUBMAT_BOUND: bound entries of that submatrix by the adjacency indicator of the induced hypercube graph on S.

So HUANG_REIDX is the glue between the matrix world and the graph world. It does not add new math, but it makes the later comparisons precise.

## Plain-language summary

HUANG_REIDX is a relabeling step. The Huang matrix is built on bitstrings, but the graph part of the proof uses numbered vertices. Reindexing just renames the rows and columns so both objects talk about the same vertex labels. This lets the proof say, entry-by-entry, that the matrix aligns with the hypercube adjacency on a subset, and then apply spectral bounds.

## Prerequisites (informal)

You only need:
- The idea that there are 2^n bitstrings of length n.
- A basic notion of a bijection (a perfect renaming).
- The definition of the Huang matrix A_n.
- The fact that |A_n| corresponds to hypercube adjacency on the original indexing.

With those, HUANG_REIDX is just a careful relabeling step that keeps the math intact while aligning the bookkeeping.
