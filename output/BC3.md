# BC3: Reindexing (Fin n -> Bool) to Fin (2^n) and transporting structure

## Intuition and motivation
The proof constantly switches between two views of the hypercube:

- **Bitstring view**: vertices are functions `Fin n -> Bool` (n-bit strings).
- **Numbered view**: vertices are `Fin (2^n)` (the numbers 0..2^n-1).

The graph and sensitivity arguments live naturally in the bitstring view. The spectral matrix arguments (Huang matrix, adjacency matrices, principal submatrices) are cleaner when vertices are numbered `0..2^n-1`. So we need a formal bridge that says:

> "These are the same vertices, just renamed."

BC3 is that bridge. It gives a *bijection* between bitstrings and numbers, then shows how to **reindex** graphs and matrices along that bijection without changing anything meaningful (adjacency, degrees, eigenvalues, trace, etc.). It is the proof's bookkeeping step that makes later comparisons precise.

Analogy: You can reorder the rows and columns of a spreadsheet, or renumber houses on a map. The data and the road network are the same; only the labels change.

## What BC3 is (from `history/breakdown.md`)
BC3 is the atomic chunk:

> "the single bridge from functions `Fin n -> Bool` to `Fin (2^n)`, letting matrices/graphs be reindexed without changing meaning."

### Dependencies (prereqs)
From the proof DAG:

- **BC0**: the Boolean cube as `Fin n -> Bool` and enumeration with `Finset.univ`.
- **BC1**: the neighbor relation / hypercube graph on those bitstrings.

### Downstream users
BC3 is used directly by:

- **HUANG_REIDX**: reindexing the Huang matrix to `Fin (2^n)`.
- **IND_GRAPH**: induced hypercube graph on a subset, reindexed to `Fin |S|`.
- **GRAPH_ISO**: graph isomorphisms that preserve degree/maxDegree across reindexing.

## Plain-language picture
There are exactly `2^n` bitstrings of length `n`. If you list them in any order, you can label them `0,1,2,...,2^n-1`. The list order does not matter; it is just a bijection. BC3 formalizes this idea:

- A *bijection* from bitstrings to numbers gives a **relabeling** of vertices.
- Relabeling a graph keeps the same edges, just with renamed endpoints.
- Relabeling a matrix keeps the same entries, just permuted rows/columns.

So reindexing is "the same object with different labels."

## Core definitions in this repo (Lean, ASCII-ized)
The key equivalence that provides the relabeling:

```lean
def boolFunEquivFin (n : ℕ) : (Fin n → Bool) ≃ Fin (2^n) :=
  (Fintype.equivFin (Fin n → Bool)).trans (finCongr (by
  norm_num [ Fintype.card_pi ]))
```

Interpretation: `Fintype.equivFin` gives a canonical bijection between any finite type and `Fin k`, so this says "bitstrings of length n are in bijection with `Fin (2^n)`."

Reindexing a matrix along this equivalence:

```lean
noncomputable def huang_matrix_fin (n : ℕ) : Matrix (Fin (2^n)) (Fin (2^n)) ℝ :=
  Matrix.reindex (boolFunEquivFin n) (boolFunEquivFin n) (huang_matrix n)
```

Reindexing the hypercube graph:

```lean
def hypercube_graph_fin (n : ℕ) : SimpleGraph (Fin (2^n)) :=
  (hypercube_graph n).map (boolFunEquivFin n).toEmbedding
```

And reindexing an induced subgraph to `Fin |S|`:

```lean
def induced_hypercube_graph_fin_card {n : ℕ} (S : Finset (Fin (2^n))) : SimpleGraph (Fin (Fintype.card {x // x ∈ S})) :=
  let G := SimpleGraph.induce (S : Set (Fin (2^n))) (hypercube_graph_fin n)
  let equiv := Fintype.equivFin {x // x ∈ S}
  G.map equiv.toEmbedding
```

## What "reindexing" means concretely
If `e : Equiv A B` is a bijection, then `Matrix.reindex e e A` is the same
matrix with rows and columns renamed:

```
B[i, j] = A[e.symm i, e.symm j]
```

This is just a permutation of rows and columns. So:

- row sums are the same (up to reordering),
- trace is the same,
- eigenvalues are the same.

The code makes this explicit:

```lean
theorem trace_reindex_eq_trace {n : Type*} [Fintype n] {m : Type*} [Fintype m] [DecidableEq n] [DecidableEq m]
  (e : n ≃ m) (A : Matrix n n ℝ) :
  Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
    simp +decide [ Matrix.trace ];
    conv_rhs => rw [ ← Equiv.sum_comp e.symm ] ;
```

Similarly, `SimpleGraph.map` relabels vertices while preserving adjacency.

## How it connects to neighboring concepts
BC3 is the "index alignment" step that lets the proof compare objects that would otherwise live on different vertex types.

### Upstream
- **BC0** provides the vertex type `Fin n -> Bool`.
- **BC1** defines adjacency on that type, which is what gets transported.

### Downstream
- **HUANG_REIDX** uses BC3 to reindex the Huang matrix so its rows/columns are `Fin (2^n)`.
- **IND_GRAPH** uses BC3 to build an induced hypercube graph on a subset and then relabel it to `Fin |S|` for a clean adjacency matrix.
- **GRAPH_ISO** uses BC3 to show that degrees and maxDegree are preserved under these relabelings, so sensitivity bounds carry over.

In the main theorem (`sensitivity_ge_sqrt_degree_of_degree_eq_n`), you can see BC3 in action:

- `S0` is a subset of bitstring vertices.
- `S` is its image in `Fin (2^n)` via `boolFunEquivFin`.
- Graph isomorphisms (`iso1`, `iso2`) certify that the induced graphs have the same degrees.

This is exactly the "bridge" role that BC3 plays.

## Tiny concrete example (n = 2)
Bitstrings: `00, 01, 10, 11` (four vertices).

Pick any bijection, for example:

```
00 -> 0
01 -> 1
10 -> 2
11 -> 3
```

The hypercube graph is a 4-cycle. If you relabel vertices by the numbers 0..3,
the graph is still a 4-cycle. The adjacency matrix is just the same matrix with rows/columns permuted.

So reindexing changes *labels*, not *structure*.

## Summary in one line
BC3 is the formal "renaming step": it turns the bitstring cube `(Fin n -> Bool)` into the numbered cube `Fin (2^n)` and shows that graphs and matrices can be transported across this renaming without changing any real mathematical content.
