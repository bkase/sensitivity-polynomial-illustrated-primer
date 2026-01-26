FULLCASE: the full-degree case (degree(f) = n)

Intuition and motivation
The Sensitivity Conjecture compares two different "complexity" measures of a Boolean
function f: its Fourier degree and its sensitivity. The general statement is about
any degree, but the proof is built around a core, stronger-looking case:

  if degree(f) = n (full degree) and n > 0, then sensitivity(f) >= sqrt(n).

Why isolate this case? Because full degree gives you a strong, concrete handle on f:
the top Fourier coefficient is nonzero. That single fact lets you construct a large,
structured subset of the hypercube and bring in Huang's spectral gadget. Once the
full-degree case is proven, the general case is handled by restricting f to a smaller
subcube where the function *does* have full degree.

What FULLCASE represents (from breakdown.md)
FULLCASE is the atomic theorem: "degree(f) = n != 0 implies sensitivity(f) >= sqrt(n)".
It is the core assembly step that combines the Fourier/level-set argument with the
Huang matrix spectral bounds.

Direct dependencies (breakdown graph):
- HUANG_SUB_LOWER: large principal submatrix -> eigenvalue >= sqrt(n).
- SPEC_UPPER: eigenvalue <= maxDegree of induced graph.
- DEG_SENS_LEVEL: degree in a level set equals sensitivity counts.
- GRAPH_ISO: reindexing preserves graph degrees (needed to align with matrices).

Direct dependents:
- REDUCE: general degree -> full degree via restriction.
- GOAL: the final theorem sensitivity(f) >= sqrt(degree(f)).
- INF_TEX: the LaTeX narrative includes this theorem as a core step.

Lean statement (the core theorem)
```lean
theorem sensitivity_ge_sqrt_degree_of_degree_eq_n {n : ℕ} (f : (Fin n → Bool) → Bool) (h_deg : degree f = n) (hn : n ≠ 0) :
  (sensitivity f : ℝ) ≥ Real.sqrt n := by
  classical
  -- Reduce to any level set with the "right" adjacency-count equality.
  have h_main :
      ∀ (S0 : Finset (Fin n → Bool)),
        (∀ x ∈ S0,
            (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S0) Finset.univ).card =
              (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y) Finset.univ).card) →
        S0.card > 2^(n-1) →
        (sensitivity f : ℝ) ≥ Real.sqrt n := by
    intro S0 h_eq hS0
    -- Reindex S0 to Fin (2^n).
    let S : Finset (Fin (2^n)) := S0.map (boolFunEquivFin n).toEmbedding
    have hS : S.card > 2^(n-1) := by
      simp [S, hS0]
    let subA := principal_submatrix_fin (huang_matrix_fin n) S
    let h_subA := principal_submatrix_fin_isSymm (huang_matrix_fin n) (huang_matrix_fin_isSymm n) S
    let evs_sub := sorted_eigenvalues subA h_subA

    -- Nonempty list witness for the spectral bounds.
    have hnS : Fintype.card {x // x ∈ S} ≠ 0 := by
      have hSpos : 0 < S.card := lt_of_le_of_lt (Nat.zero_le _) hS
      rw [Fintype.card_coe]
      exact ne_of_gt hSpos
    have h_ne : evs_sub ≠ [] := by
      apply List.ne_nil_of_length_pos
      dsimp [evs_sub]
      rw [sorted_eigenvalues_length]
      exact Nat.pos_of_ne_zero hnS

    -- Lower bound on λ_max from interlacing.
    have hpos_sub : 0 < Fintype.card {x // x ∈ S} := by
      exact Fintype.card_pos_iff.mpr
        ⟨ ⟨ Classical.choose (Finset.card_pos.mp (pos_of_gt hS)),
            Classical.choose_spec (Finset.card_pos.mp (pos_of_gt hS)) ⟩ ⟩
    have h_ne0 : evs_sub ≠ [] := by
      apply List.ne_nil_of_length_pos
      dsimp [evs_sub]
      rw [sorted_eigenvalues_length]
      exact hpos_sub
    have h_lower0 :
        Real.sqrt n ≤ evs_sub.getLast h_ne0 := by
      simpa [subA, h_subA, evs_sub, h_ne0] using
        (huang_submatrix_max_eigenvalue_ge_sqrt_n (n := n) hn S hS)
    have h_lower : Real.sqrt n ≤ evs_sub.getLast h_ne := by
      have h_eq_last :
          evs_sub.getLast h_ne0 = evs_sub.getLast h_ne := by
        exact
          (List.getLast_congr (l₁ := evs_sub) (l₂ := evs_sub)
            (h₁ := h_ne0) (h₂ := h_ne) (h₃ := rfl))
      rw [← h_eq_last]
      exact h_lower0

    -- Upper bound on λ_max by max degree of the induced graph.
    have h_adj :
        ∀ i j,
          |subA i j| ≤ if (induced_hypercube_graph_fin_card S).Adj i j then 1 else 0 := by
      intro i j
      simpa [subA] using (huang_submatrix_bounded_by_induced_adjacency (S := S) i j)
    have h_lambda_le_max :
        evs_sub.getLast h_ne ≤ (induced_hypercube_graph_fin_card S).maxDegree := by
      simpa [subA, h_subA, evs_sub, h_ne] using
        (spectral_radius_bound (A := subA) (hA := h_subA)
          (G := induced_hypercube_graph_fin_card S) h_adj hnS)

    -- Max degree of the induced graph is at most sensitivity.
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

    have h_maxDegree_le : (induced_hypercube_graph_fin_card S).maxDegree ≤ sensitivity f := by
      refine SimpleGraph.maxDegree_le_of_forall_degree_le (G := induced_hypercube_graph_fin_card S)
        (k := sensitivity f) ?_
      intro i
      let v0 := iso.symm i
      have hdeg : (induced_hypercube_graph_fin_card S).degree i = G0.degree v0 := by
        classical
        have hcard := Fintype.card_congr (iso.mapNeighborSet v0)
        have hiso :
            (induced_hypercube_graph_fin_card S).degree (iso v0) = G0.degree v0 := by
          calc
            (induced_hypercube_graph_fin_card S).degree (iso v0) =
                Fintype.card ((induced_hypercube_graph_fin_card S).neighborSet (iso v0)) := by
                  symm
                  simpa using
                    (SimpleGraph.card_neighborSet_eq_degree
                      (G := induced_hypercube_graph_fin_card S) (v := iso v0))
            _ = Fintype.card (G0.neighborSet v0) := by
                  simpa using hcard.symm
            _ = G0.degree v0 := by
                  simpa using (SimpleGraph.card_neighborSet_eq_degree (G := G0) (v := v0))
        have hv0 : iso v0 = i := by
          -- `iso` is an equivalence; rewrite with `Equiv.apply_symm_apply`.
          simp [v0]
        have hiso' := hiso
        rw [hv0] at hiso'
        exact hiso'
      rw [hdeg]
      exact h_deg_le_G0 v0

    -- Combine the bounds.
    have h_maxDegree_le' : (induced_hypercube_graph_fin_card S).maxDegree ≤ (sensitivity f : ℕ) := h_maxDegree_le
    have h_upper : evs_sub.getLast h_ne ≤ (sensitivity f : ℝ) := by
      exact le_trans h_lambda_le_max (by exact_mod_cast h_maxDegree_le')

    exact le_trans h_lower h_upper

  -- Pick the large level set (S_pos or S_neg).
  have h_large := exists_large_level_set f h_deg hn
  cases h_large with
  | inl hpos =>
      apply h_main (S_pos f)
      · intro x hx
        simpa using (sensitivity_at_x_eq_degree_in_S_pos f x hx).symm
      · exact hpos
  | inr hneg =>
      apply h_main (S_neg f)
      · intro x hx
        simpa using (sensitivity_at_x_eq_degree_in_S_neg f x hx).symm
      · exact hneg
```

Plain-language proof sketch (step by step)
1) Start with full degree -> imbalance.
   Full degree means the top Fourier coefficient (the one on the full set [n])
   is nonzero. The proof defines a signed version of f:

   g(x) = (if f(x) then -1 else 1) * chi_univ(x).

   Because the top coefficient is nonzero, the average (sum) of g over the cube
   is nonzero. That means g outputs +1 and -1 *unequally* often.

   Analogy: Think of a checkerboard (chi_univ) painted with f's colors. The full
   degree condition guarantees that after flipping colors in a checkerboard pattern,
   you do not get a perfectly balanced board. One color must appear more than half.

2) Large level set.
   Let S_pos = {x | g(x) = 1} and S_neg = {x | g(x) = -1}.
   Since their sizes are unequal and together they cover all 2^n vertices, one of
   them has size > 2^(n-1). Call that large set S.

3) Sensitivity becomes degree in the induced subgraph (DEG_SENS_LEVEL).
   The hypercube graph Q_n has vertices as inputs and edges between inputs that
   differ in one bit. There is a parity flip along every edge, so chi_univ changes
   sign along edges. That leads to the key equivalence:

   along an edge x ~ y:
     g(x) = g(y)  <->  f(x) != f(y).

   This means: for a vertex in a level set S (where g is constant), its neighbors
   *inside S* are exactly the neighbors where f flips. So, within S, the degree
   of a vertex equals its sensitivity count. In particular, the max degree of the
   induced subgraph on S is <= sensitivity(f).

4) Bring in the Huang matrix.
   The Huang matrix A_n is a signed adjacency-like matrix for the hypercube.
   It has a very clean spectrum: eigenvalues are +sqrt(n) and -sqrt(n), each with
   multiplicity 2^(n-1). Two spectral facts are used:

   - HUANG_SUB_LOWER: If you take a principal submatrix A_n[S] for a set S with
     |S| > 2^(n-1), then the largest eigenvalue of A_n[S] is at least sqrt(n)
     (this uses interlacing).
   - SPEC_UPPER: The largest eigenvalue of a matrix whose entries are bounded
     by the adjacency of a graph is at most the max degree of that graph.

   The second fact is applied by comparing |A_n[S]| to the adjacency matrix of
   the induced subgraph on S. This gives:

     sqrt(n) <= lambda_max(A_n[S]) <= maxDegree(induced graph on S).

5) Combine with the sensitivity connection.
   Because maxDegree(induced graph on S) <= sensitivity(f), we get:

     sensitivity(f) >= sqrt(n).

   This is exactly FULLCASE.

Key snippets that show the connections
Signed transform and level sets (Lean):
```lean
def g_val {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℝ :=
  (if f x then -1 else 1) * chi Finset.univ x

def S_pos {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.filter (fun x => g_val f x = 1) Finset.univ

def S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.filter (fun x => g_val f x = -1) Finset.univ
```

Sensitivity as max neighbor count (informal math):
```
sensitivity(f) = max_x |{ y : x ~ y and f(x) != f(y) }|
```

Spectral sandwich (informal):
```
sqrt(n) <= lambda_max(A_n[S]) <= maxDegree(induced graph on S) <= sensitivity(f).
```

How FULLCASE connects to neighboring concepts
- Prerequisites it uses:
  - Fourier degree and the fact that degree(f) = n implies the top coefficient is
    nonzero (FULLCOEF/GVAL0).
  - The g-transform and the "large level set" fact (LEVELSETS).
  - The neighbor parity rule (NEIGH_PARITY/NEIGH_RULE), which makes degree in the
    level set equal sensitivity (DEG_SENS_LEVEL).
  - Huang matrix spectral lower bound for large submatrices (HUANG_SUB_LOWER).
  - Spectral upper bound via max degree (SPEC_UPPER).
  - Reindexing glue (GRAPH_ISO) to align hypercube vertices with matrix indices.

- What it enables:
  - REDUCE: any function of degree k is restricted to a k-dimensional subcube,
    giving full degree and allowing FULLCASE to apply.
  - GOAL: the final inequality sensitivity(f) >= sqrt(degree(f)).

If you want to read just one proof chunk before FULLCASE, read the part that
explains why the large level set forces a big eigenvalue (HUANG_SUB_LOWER), and
the part that identifies induced degree with sensitivity (DEG_SENS_LEVEL). Those
are the two "bridges" that make the spectral bound translate into a sensitivity
bound.
