# IND_GRAPH: induced hypercube graph on a subset

## Intuition and motivation
In the proof, we keep looking at the Boolean hypercube: all n-bit strings, with an edge between two strings that differ in exactly one bit. We then pick a special subset of vertices S (a "level set" of a transformed function g). The key quantity we care about is: for each vertex in S, how many of its hypercube neighbors are also in S? That number is just the degree of the vertex in the graph induced by S.

So IND_GRAPH is the formal step that says: "Given S, build the induced subgraph of the hypercube on S." This lets us talk about degrees, max degree, and adjacency matrices on S alone. It also aligns the vertex indexing so we can compare a submatrix of the Huang matrix with the adjacency matrix of this induced graph.

Think of it like this: you have a huge social network (the hypercube). You highlight a subset S of people. The induced subgraph is the smaller network you get by keeping only those people and only their mutual connections. Then you relabel those people 0, 1, 2, ..., |S|-1 so that you can write their connections as a square matrix.

## Plain-language definition
1. **Hypercube graph Q_n**: vertices are all n-bit strings. Two vertices are adjacent if they differ in exactly one bit.
2. **Induced subgraph on S**: keep only the vertices in S, and keep an edge between two of them if (and only if) they were adjacent in the full hypercube.
3. **Reindexing to Fin |S|**: instead of naming vertices by their original bitstrings, we relabel the vertices of S as 0, 1, ..., |S|-1. This is purely a bookkeeping step that makes matrices line up cleanly.

## Where it appears in this repo (Lean snippets)
The hypercube graph is defined by Hamming distance 1:

```lean
def hypercube_graph (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun x y => (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1)
```

The induced hypercube graph on a subset S of vertices (no reindexing yet):

```lean
def induced_hypercube_graph {n : ℕ} (S : Finset (Fin n → Bool)) : SimpleGraph {x // x ∈ S} :=
  SimpleGraph.induce (S : Set (Fin n → Bool)) (hypercube_graph n)
```

The version that reindexes vertices to `Fin |S|` (this is the IND_GRAPH atom in the breakdown):

```lean
def induced_hypercube_graph_fin_card {n : ℕ} (S : Finset (Fin (2^n))) : SimpleGraph (Fin (Fintype.card {x // x ∈ S})) :=
  let G := SimpleGraph.induce (S : Set (Fin (2^n))) (hypercube_graph_fin n)
  let equiv := Fintype.equivFin {x // x ∈ S}
  G.map equiv.toEmbedding
```

Explanation of that last definition:
- `hypercube_graph_fin n` is the hypercube graph reindexed from bitstrings to `Fin (2^n)`.
- `SimpleGraph.induce` keeps only vertices in S and edges between them.
- `Fintype.equivFin {x // x ∈ S}` gives a bijection from the subset to `Fin |S|`, i.e., relabeling.
- `G.map` applies the relabeling to the graph, producing a graph whose vertices are `0..|S|-1`.

## Where it shows up in the LaTeX notes
The notes refer to the induced subgraph on S and its adjacency matrix:

```tex
Let $H_1$ be the adjacency matrix of $(Q_n)_S$.
```

Here `(Q_n)_S` is exactly the induced subgraph of the hypercube on S. The adjacency matrix `H_1` is what you get after the reindexing step.

## How it connects to neighboring atoms
- **Depends on**:
  - **BC2**: the notion of an induced subgraph and graph statistics (degree, maxDegree).
  - **BC3**: reindexing from bitstrings to `Fin (2^n)`, so matrix indices match graph vertices.

- **Used by**:
  - **SUBMAT_BOUND**: compares entries of a principal submatrix of the Huang matrix with the adjacency matrix of this induced graph.
  - Then **SPEC_UPPER** and later steps use the induced graph's max degree to bound eigenvalues and finally sensitivity.

## Tiny concrete example
Let n = 3 and take
```
S = {000, 001, 011, 010}.
```
These four vertices form a square in the 3-cube. The induced graph on S is exactly a 4-cycle: each vertex has degree 2 inside S. If we reindex S as {0,1,2,3}, the adjacency matrix is a 4x4 matrix with two 1s in each row.

This is the same graph you would use to count "neighbors that stay inside S," which is the quantity that later matches sensitivity.

## Takeaway
IND_GRAPH is the formal object that turns "the subset S of cube vertices" into a graph with a clean, matrix-friendly indexing. It is the bridge between the combinatorial world (neighbors, degrees) and the linear-algebra world (submatrices, eigenvalues).
