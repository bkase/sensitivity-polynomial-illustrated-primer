# BC2: Induced subgraphs + degree/maxDegree

## Intuition and motivation
The proof keeps bouncing between two views of the same object:

- A boolean function on the hypercube (inputs are vertices).
- A graph on those vertices (edges are "neighbors" that differ in one bit).

When we zoom in on a special subset of vertices (like a level set of a transformed function), we still want to talk about "how connected" those vertices are **inside the subset**. That is exactly what an induced subgraph does: it keeps every vertex in the subset and **all** edges between them. Once we have that induced graph, two simple statistics become the workhorses:

- **degree** of a vertex = how many neighbors it has *within the subset*,
- **maxDegree** of a graph = the largest degree among all vertices.

These are the numbers that connect sensitivity counts to spectral bounds. Without induced subgraphs and degree/maxDegree, the proof cannot translate "how often the function flips" into "how big an eigenvalue can be."

## Plain-language picture
Think of the hypercube graph as a giant social network:

- Vertices are people.
- Edges are "friend" links (differ in one bit).

Now pick a club S of people (a subset of vertices). The **induced subgraph** is "the club's internal friendship network": everyone in S is still there, and **every friendship link between club members is kept**.

For any person in the club:

- Their **degree** is the number of friends they have *inside the club*.
- The **maxDegree** is the most-connected person in the club.

That is exactly the combinatorial data the proof needs.

## What BC2 is (from `history/breakdown.md`)
BC2 is the atomic chunk that introduces:

- The **induced subgraph** operation.
- The **degree** of a vertex in a graph.
- The **maxDegree** of a graph.

### Dependencies (prereqs)
From the proof DAG:

- **BC1**: the neighbor relation / hypercube graph `Q_n` (edges are Hamming distance 1).
- Indirectly **BC0**: the Boolean cube `Fin n -> Bool` is the vertex type.

### Downstream users
BC2 directly feeds these later chunks:

- **DEG_SENS_LEVEL**: sensitivity equals degree in an induced subgraph of a level set.
- **IND_GRAPH**: the induced hypercube graph on a subset.
- **SPEC_UPPER**: spectral bound uses `maxDegree`.
- **GRAPH_ISO**: reindexing preserves degrees/maxDegree.

## The core definitions in this repo
Lean definition of the induced subgraph on a subset of hypercube vertices (ASCII-ized; read `in` as set membership):

```lean
def induced_hypercube_graph {n : ℕ} (S : Finset (Fin n → Bool)) : SimpleGraph {x // x ∈ S} :=
  SimpleGraph.induce (S : Set (Fin n → Bool)) (hypercube_graph n)
```

Read this as: "take the hypercube graph and **induce** it on the vertex subset `S`."

There is also a version after reindexing to `Fin (2^n)` and then to `Fin |S|`, used later for matrix indexing:

```lean
def induced_hypercube_graph_fin_card {n : ℕ} (S : Finset (Fin (2^n))) : SimpleGraph (Fin (Fintype.card {x // x ∈ S})) :=
  let G := SimpleGraph.induce (S : Set (Fin (2^n))) (hypercube_graph_fin n)
  let equiv := Fintype.equivFin {x // x ∈ S}
  G.map equiv.toEmbedding
```

The degree and maxDegree are the standard SimpleGraph statistics in Lean:

- `G.degree v` = number of neighbors of `v`.
- `G.maxDegree` = maximum of `G.degree` over all vertices.

Those are not redefined here; the file uses Mathlib's definitions.

## How it connects to sensitivity (neighboring chunk: DEG_SENS_LEVEL)
Sensitivity counts how many neighbors flip the function value. After the `g` transform and the level-set split `S_pos` / `S_neg`, neighbors with `f` flipping become exactly neighbors that **stay inside the same level set**.

The Lean lemma below is the formal statement of that idea (shown for `S_pos`, ASCII-ized):

```lean
lemma sensitivity_at_x_eq_degree_in_S_pos {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : x ∈ S_pos f) :
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y) Finset.univ).card =
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S_pos f) Finset.univ).card := by
  ...
```

Translated: "for a vertex `x` in the positive level set, the number of neighbors where `f` flips equals the number of neighbors **inside** that level set." That right-hand side is exactly the **degree of `x` in the induced subgraph on `S_pos`**. So:

- sensitivity at `x` = degree in the induced subgraph,
- therefore max sensitivity is at least the **maxDegree** of that induced subgraph.

This is the combinatorial bridge that lets later matrix bounds talk about sensitivity.

## How it connects to the spectral bound (neighboring chunk: SPEC_UPPER)
In the LaTeX notes, the induced subgraph appears as a principal submatrix of the adjacency matrix:

```tex
Let H_1 be the adjacency matrix of (Q_n)_S.
It is obtained by deleting some rows and the corresponding columns of the matrix for B_n.
Then lambda_1(H_1) <= d_S(g) because the weight of a row is at most d_S(g).
```

Here `d_S(g)` is the max degree in the induced subgraph on `S`. A row of the adjacency matrix has a 1 for each neighbor inside `S`, so its row sum equals the degree of that vertex. The maximum row sum is exactly `maxDegree`.

Lean uses this as a reusable lemma (`spectral_radius_bound`):

```lean
theorem spectral_radius_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (G : SimpleGraph (Fin n))
  (h_adj : ∀ i j, |A i j| ≤ if G.Adj i j then 1 else 0) (hn : n ≠ 0) :
  let evs := sorted_eigenvalues A hA
  let lambda_max := evs.getLast (List.ne_nil_of_length_pos (by rw [sorted_eigenvalues_length A hA]; exact Nat.pos_of_ne_zero hn))
  lambda_max ≤ G.maxDegree := by
  ...
```

So BC2 supplies the graph statistic (`maxDegree`) that upper-bounds the largest eigenvalue of the submatrix. This is the matrix-to-graph bridge that lets the final inequality close.

## Summary in one line
BC2 is the "zoom-in-and-count" step: take a subset of hypercube vertices, keep all edges among them (induced subgraph), and use degree/maxDegree as the numeric handle that links sensitivity to spectral bounds.
