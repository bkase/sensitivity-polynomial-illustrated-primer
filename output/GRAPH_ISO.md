# GRAPH_ISO: Graph isomorphisms under reindexing

## Intuition and motivation (why we need this)
In this proof we keep switching between two ways to name the same vertices of the hypercube:
1. As bitstrings (functions `Fin n -> Bool`).
2. As numbers `0,1,...,2^n-1` (the type `Fin (2^n)`), which is convenient for matrices.

Matrix arguments (spectral bounds) want vertices labeled by consecutive integers so rows and columns are indexed cleanly. Sensitivity arguments live on the original bitstring hypercube. GRAPH_ISO is the glue that says: renaming vertices does not change the graph. If two graphs differ only by a relabeling, they have the same adjacency pattern and the same degrees. This lets us transfer degree bounds from the "bitstring world" to the "matrix world."

Analogy: You can renumber houses on a city map, but the roads are the same. Every house still has the same number of roads attached, even if the house numbers change.

## Plain-language concept
A graph is just vertices with edges. An isomorphism between graphs is a one-to-one relabeling of vertices that preserves edges:

```
phi : V -> V'  (a bijection)
u ~ v in G   <->   phi(u) ~ phi(v) in G'
```

If `phi` is an isomorphism, then adjacency is preserved. In particular, the number of neighbors (degree) is preserved:

```
deg_G(u) = deg_G'(phi(u))
maxDegree(G) = maxDegree(G')
```

So if you bound the degree in one labeling, you have the same bound in every relabeling.

## Where this sits in the proof
GRAPH_ISO appears when we take a large level set `S0` (a subset of the hypercube) and move it into the indexing used by the Huang matrix:

1. Start with `S0` inside `(Fin n -> Bool)`, the original hypercube vertices.
2. Map it to `S` inside `Fin (2^n)` using a bijection that reindexes bitstrings as numbers.
3. Reindex again to `Fin |S|` so the induced subgraph lines up with a `|S| x |S|` principal submatrix.

GRAPH_ISO states these induced graphs are isomorphic, so degrees and maxDegree are unchanged by the reindexing. This is exactly what we need to compare:
- the graph-degree side (sensitivity, defined on bitstrings), and
- the matrix side (spectral bounds, indexed by `Fin (2^n)` and `Fin |S|`).

## Lean/code anchors (what it looks like in the formalization)
The key graph definitions and the equivalence between `S0` and `S` are:

```lean
let G0 : SimpleGraph {x // x ∈ (S0 : Set (Fin n → Bool))} :=
  (hypercube_graph n).induce (S0 : Set (Fin n → Bool))
let G1 : SimpleGraph {x // x ∈ (S : Set (Fin (2^n)))} :=
  (hypercube_graph_fin n).induce (S : Set (Fin (2^n)))
-- Prefer the `Subtype.fintype` instance to avoid instance mismatch in neighbor finsets.
letI : Fintype {x // x ∈ (S0 : Set (Fin n → Bool))} := by
  classical
  exact (Subtype.fintype (p := fun x => x ∈ (S0 : Set (Fin n → Bool))))
let eS : {x // x ∈ (S0 : Set (Fin n → Bool))} ≃ {x // x ∈ (S : Set (Fin (2^n)))} :=
  { toFun := fun x =>
      ⟨ (boolFunEquivFin n) x.1,
        by
          have hx0 : x.1 ∈ S0 := by
            exact Finset.mem_coe.mp x.2
          show (boolFunEquivFin n) x.1 ∈ S
          exact Finset.mem_map.mpr ⟨ x.1, hx0, rfl ⟩ ⟩
    invFun := fun y =>
      ⟨ (boolFunEquivFin n).symm y.1,
        by
          have hy : y.1 ∈ S := by
            exact Finset.mem_coe.mp y.2
          rcases Finset.mem_map.mp hy with ⟨ x0, hx0, hx0eq ⟩
          have hx0eq' : (boolFunEquivFin n).symm y.1 = x0 := by
            have h := congrArg (fun z => (boolFunEquivFin n).symm z) hx0eq
            simp at h
            exact h.symm
          have hx0' : (boolFunEquivFin n).symm y.1 ∈ S0 := by
            rw [hx0eq']
            exact hx0
          exact hx0' ⟩
    left_inv := by
      intro x; ext; simp
    right_inv := by
      intro y; ext; simp }
```

Later, the proof constructs explicit graph isomorphisms between these induced graphs:

```lean
let iso1 : G0 ≃g G1 :=
  { toEquiv := eS
    map_rel_iff' := by
      intro a b
      -- Reduce to adjacency in the base graphs, then use the map-adj lemma.
      change (hypercube_graph_fin n).Adj (eS a).1 (eS b).1 ↔ (hypercube_graph n).Adj a.1 b.1
      simp [hypercube_graph_fin, eS] }
let equivS := Fintype.equivFin {x // x ∈ S}
have iso2 : G1 ≃g induced_hypercube_graph_fin_card S := by
  dsimp [induced_hypercube_graph_fin_card, G1]
  exact SimpleGraph.Iso.map equivS G1
let iso : G0 ≃g induced_hypercube_graph_fin_card S := iso2.comp iso1
```

The point of `iso` is: adjacency and degree are preserved under these reindexings.

The key lemma `h_deg_le_G0` shows that every vertex in the induced graph `G0` has degree at most `sensitivity f`:

```lean
have h_deg_le_G0 : ∀ v0 : {x // x ∈ S0}, G0.degree v0 ≤ sensitivity f := by
  intro v0
  have h_map := SimpleGraph.map_neighborFinset_induce
    (G := hypercube_graph n) (s := (S0 : Set (Fin n → Bool))) v0
  have h_card :
      (G0.neighborFinset v0).card =
        ((hypercube_graph n).neighborFinset v0 ∩ S0).card := by
    have h_card' := congrArg Finset.card h_map
    simpa [G0, Finset.card_map, Finset.toFinset_coe, -SimpleGraph.card_neighborFinset_eq_degree] using
      h_card'
  have h_filter :
      (hypercube_graph n).neighborFinset v0 ∩ S0 =
        Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ y ∈ S0) Finset.univ := by
    ext y
    simp [SimpleGraph.neighborFinset_eq_filter, Finset.mem_inter, Finset.mem_filter]
  have h_degree_formula :
      G0.degree v0 =
        (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ y ∈ S0) Finset.univ).card := by
    have h_card'' :
        (G0.neighborFinset v0).card =
          (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ y ∈ S0) Finset.univ).card := by
      rw [← h_filter]
      exact h_card
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact h_card''
  have h_eq' := h_eq v0.1 (by exact Finset.mem_coe.mp v0.2)
  have h_card_le :
      (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ f v0 ≠ f y) Finset.univ).card
        ≤ sensitivity f := by
    unfold sensitivity
    have :=
      Finset.le_sup (s := Finset.univ)
        (f := fun x =>
          Finset.card
            (Finset.filter
              (fun y =>
                (Finset.card
                    (Finset.filter (fun i => x i ≠ y i) Finset.univ) = 1) ∧ f x ≠ f y)
              Finset.univ))
        (by simp : (v0 : Fin n → Bool) ∈ (Finset.univ : Finset (Fin n → Bool)))
    simp [hypercube_graph_adj]
    exact this
  calc
    G0.degree v0
        = (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ y ∈ S0) Finset.univ).card := h_degree_formula
    _ = (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ f v0 ≠ f y) Finset.univ).card := h_eq'
    _ ≤ sensitivity f := h_card_le
```

## How it connects to neighboring atoms
Prerequisites (from `history/breakdown.md`):
- BC2: induced subgraph and degree/maxDegree definitions.
- BC3: the reindexing equivalence between `Fin n -> Bool` and `Fin (2^n)`.
(BC1, the hypercube adjacency relation, is an implicit base for these.)

Downstream use:
- FULLCASE (the core full-degree theorem) uses GRAPH_ISO to justify that the
  maxDegree bound obtained on the reindexed induced graph is the same maxDegree
  coming from sensitivity on the original hypercube.

In short: GRAPH_ISO is the proof's "renaming is harmless" principle, which is
essential for comparing the graph-based sensitivity bounds with the
matrix-based spectral bounds.
