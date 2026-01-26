# BC1 - Neighbor relation / hypercube graph Q_n

Intuition and motivation
We want to measure how a boolean function changes when we flip exactly one input bit. That "one-bit flip" is the basic local move on the Boolean cube, and sensitivity is exactly a count of how many such local moves change the function value. So before we can define sensitivity or talk about graphs and adjacency matrices, we need a precise notion of "neighbor" on the cube. BC1 supplies that: it turns the set of all n-bit strings into the hypercube graph Q_n by connecting two inputs that differ in exactly one bit.

Plain-language definition
- The vertices are all n-bit strings (from BC0).
- Two vertices are neighbors if you can go from one to the other by flipping exactly one bit.
- The resulting graph is the n-dimensional hypercube Q_n.

Analogy: imagine n on/off switches. Each vertex is one switch setting. A neighbor is what you get by flipping a single switch. The hypercube graph is the wiring diagram of all possible one-switch flips.

In math shorthand, "neighbors" means Hamming distance 1:
```
x ~ y  <=>  |{ i in [n] : x_i != y_i }| = 1
```
So each vertex has exactly n neighbors (one for each coordinate you can flip).

How it appears in the LaTeX notes
The lecture notes introduce the neighbor relation as the graph underlying sensitivity:
```tex
We can start to look at this as a graph and write $x \sim y$ if they differ in only 1 bit. We call this graph $Q_n$.
\[
s(f) := \max_{x} |\{y \mid x \sim y, f(x) \neq y\}|
\]
```
This is BC1 in action: the adjacency relation x ~ y is the primitive notion used to define sensitivity.

How it is formalized in Lean
In the Lean file, the hypercube graph is defined as a SimpleGraph on functions `Fin n -> Bool`. Two vertices are adjacent if the set of coordinates where they differ has cardinality 1.
```lean
def hypercube_graph (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun x y => (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1)

lemma hypercube_graph_adj {n : ℕ} (x y : Fin n → Bool) :
  (hypercube_graph n).Adj x y ↔ (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1 := by
    simp [hypercube_graph];
    -- If x and y are not equal, then there must be at least one index where they differ. The cardinality of the set of such indices being 1 means there's exactly one difference, which implies x and y are not equal. Conversely, if the cardinality is 1, then there's exactly one difference, so x and y can't be equal.
    apply Iff.intro;
    · simp_all +decide [ eq_comm ];
    · aesop
```
Read `Fin n -> Bool` as "an n-bit string." The `Finset.filter` collects the indices where two strings differ; `card = 1` enforces "exactly one bit flips."

Connections in the proof graph
What BC1 depends on:
- BC0 (Hypercube vertices + enumeration). We need a universe of vertices (all n-bit strings) before we can define adjacency.

What depends on BC1:
- BC2 (Induced subgraphs + degree/maxDegree). Once you have adjacency, you can talk about induced subgraphs and degrees.
- BC3 (Reindexing). Adjacency must be preserved when reindexing the cube to `Fin (2^n)` for matrix work.
- SEN0 (Sensitivity). Sensitivity is defined by counting neighbors where f changes.
- NEIGH_PARITY (Neighbor parity flip). If two vertices are neighbors, their parity differs; this powers the g-transform step.

Why this matters downstream
BC1 is the hinge between "functions on the Boolean cube" and "graph theory / spectral tools." It lets the proof:
- Translate sensitivity into a graph degree question (counting adjacent changes).
- Define adjacency matrices for Q_n (used to compare with the Huang matrix).
- Use parity behavior of neighbors to relate the transformed function g to the original function f.

If you only remember one thing: BC1 says "one-bit flip equals an edge." That single idea is what turns local changes of a boolean function into graph structure the rest of the proof can analyze.
