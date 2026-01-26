# SUBMAT_BOUND

## Intuition and motivation
At this point in the proof, we have two worlds that need to talk to each other:

- A **matrix world** (the Huang matrix) where we can talk about eigenvalues.
- A **graph world** (the hypercube and its induced subgraphs) where we can talk about degrees and sensitivity.

Eigenvalue tools usually need a matrix inequality of the form "every entry of this matrix is small, and it is zero where there is no edge." The **SUBMAT_BOUND** atom is exactly that bridge. It takes a *submatrix* of the Huang matrix (so we are only looking at a subset of vertices) and says: **entry-by-entry, its absolute values are bounded by the adjacency indicator of the induced subgraph**.

Without this bound, we cannot apply the "spectral radius <= max degree" lemma later, so the whole eigenvalue-to-degree comparison would be missing its key hypothesis.

## What SUBMAT_BOUND says (plain language)
Imagine a big table of connections between vertices, where each entry is:

- `+1` or `-1` if two vertices are connected by an edge in the hypercube, and
- `0` if they are not connected.

That table is the Huang matrix (after reindexing). Now pick a subset `S` of vertices and "crop" the table to just those rows and columns. That cropped table is the **principal submatrix**.

The induced graph on `S` has an adjacency indicator: it is `1` when two vertices in `S` are neighbors in the hypercube, and `0` otherwise.

**SUBMAT_BOUND** says: for every pair of vertices in `S`,

```
abs(entry of the cropped Huang matrix) <= adjacency_indicator_in_induced_graph
```

So:
- if there is **no edge** between the two vertices in the induced graph, the matrix entry must be `0`;
- if there **is an edge**, the matrix entry is at most `1` in absolute value (it can be `+1` or `-1`).

This is exactly the "no phantom edges, no oversized weights" guarantee needed later.

## How it is proved (plain-language sketch)
There are two ingredients:

1. **Huang matrix adjacency fact**: the absolute value of each Huang matrix entry equals the adjacency indicator of the hypercube. In symbols,
   ```
   abs(A_n_fin[i,j]) = 1 if i and j are adjacent, else 0
   ```
2. **Restriction to a subset**: when you take a principal submatrix on `S`, you are just restricting to rows/columns for vertices in `S`. The induced graph on `S` uses exactly those same vertices and edges.

So when you restrict the matrix, the same adjacency rule holds, but now only for vertices in `S`. That is the SUBMAT_BOUND inequality.

## Lean snippet (with explanation)
The Lean statement that captures SUBMAT_BOUND is:

```lean
lemma huang_submatrix_bounded_by_induced_adjacency {n : ℕ} (S : Finset (Fin (2^n))) (i j : Fin (Fintype.card {x // x ∈ S})) :
  |principal_submatrix_fin (huang_matrix_fin n) S i j| ≤ if (induced_hypercube_graph_fin_card S).Adj i j then 1 else 0 := by
    unfold principal_submatrix_fin induced_hypercube_graph_fin_card;
    simp +decide [ principal_submatrix ];
    split_ifs <;> simp_all +decide [ abs_huang_fin_eq_adjacency_fin ];
    · split_ifs <;> norm_num;
    · rename_i h;
      contrapose! h;
      use (Fintype.equivFin { x // x ∈ S }).symm i, by
        exact Finset.mem_coe.mp ( Subtype.mem _ ), (Fintype.equivFin { x // x ∈ S }).symm j, by
        exact ( Fintype.equivFin { x // x ∈ S } ).symm j |>.2
      generalize_proofs at *;
      aesop
```

Read it as:
- `principal_submatrix_fin (huang_matrix_fin n) S` is the Huang matrix restricted to `S` and reindexed to `Fin |S|`.
- `(induced_hypercube_graph_fin_card S).Adj i j` is the adjacency predicate of the induced graph on `S`, also reindexed to `Fin |S|`.
- The inequality is **entrywise**, and it uses absolute values because the Huang matrix has `+1` and `-1` entries.

The proof uses another lemma (the reindexed adjacency fact):

```lean
lemma abs_huang_fin_eq_adjacency_fin {n : ℕ} (i j : Fin (2^n)) :
  |huang_matrix_fin n i j| = if (hypercube_graph_fin n).Adj i j then 1 else 0 := by
    -- Apply the result that |huang_matrix u v| = 1 if u~v else 0.
    have h_abs : ∀ u v : Fin n → Bool, |(huang_matrix n) u v| = if (hypercube_graph n).Adj u v then 1 else 0 := by
      -- By definition of $A_n$, we know that $|A_n u v| = 1$ if $u$ and $v$ are adjacent in the hypercube graph, and $|A_n u v| = 0$ otherwise.
      intros u v
      simp [abs_huang_eq_adjacency, hypercube_graph];
      by_cases h : u = v <;> simp +decide [ h, eq_comm ];
    unfold huang_matrix_fin;
    unfold hypercube_graph_fin; aesop;
```

Then it restricts that statement to the subset `S` and matches the induced graph definition.

## How it connects to neighboring steps
Think of SUBMAT_BOUND as a **bridge** between matrix entries and graph edges.

- **Inputs it depends on (from breakdown.md)**:
  - **SUBMAT**: defines the principal submatrix `A_n_fin[S]`.
  - **IND_GRAPH**: defines the induced hypercube graph on `S`.
  - **HUANG_REIDX**: ensures the Huang matrix and the graph are indexed the same way (so the entrywise comparison even makes sense).

- **Directly used by**:
  - **SPEC_UPPER**: the spectral upper bound lemma, which needs the entrywise inequality to show
    `lambda_max(A_n_fin[S]) <= maxDegree(induced graph on S)`.

- **Downstream impact**:
  - The max-degree bound ties into sensitivity (via the induced graph of a level set).
  - Together with the interlacing lower bound, this forces sensitivity to be at least `sqrt(n)`.

So SUBMAT_BOUND is the precise "interface condition" that lets matrix eigenvalues talk to graph degrees in the proof.

## Quick analogy
If the Huang matrix is a *signed road map* (roads have a direction sign +/−), then the induced graph is the *unsigned road map* of a neighborhood. SUBMAT_BOUND says: when you crop the signed map to that neighborhood, every road you see really exists in the unsigned map, and every road has weight at most 1. This is exactly what you need before counting roads (degrees) can control spectral properties.
