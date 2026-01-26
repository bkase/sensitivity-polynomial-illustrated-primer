# GOAL: final Sensitivity Conjecture inequality

## Intuition and motivation
The Sensitivity Conjecture compares two different ways of measuring how "complex"
or "fragile" a Boolean function is. One measure (degree) asks: what is the largest
group of inputs that can interact together in the function's Fourier expansion?
The other measure (sensitivity) asks: is there an input where many single-bit
flips change the output?

GOAL is the statement that these two measures are tightly linked: if the function
has high degree, it must be sensitive somewhere. This is the endpoint of the proof
because it gives the promised inequality for *every* Boolean function, not just
for a special case.

Analogy: Think of a device with many on/off switches. "Degree" is the size of the
largest interaction that ever matters (a rule that depends on many switches at
once). "Sensitivity" is how many single switches can flip the output at the most
fragile input. GOAL says: if your device ever has a rule involving many switches,
then there is some input where lots of single switches can flip the output.

## What GOAL represents (from `history/breakdown.md`)
**Represents:** The final theorem in Lean:
```
sensitivity(f) >= sqrt(degree(f))
```

**Depends on:**
- **FULLCASE**: the full-degree theorem `degree(f) = n != 0 -> sensitivity(f) >= sqrt(n)`.
- **REDUCE**: the reduction from general degree to the full-degree case by restriction.
- **REPO** is the overall project context that frames the goal.

**What depends on it:** Nothing downstream. GOAL is the final endpoint of the proof.

## The statement in plain language
For any Boolean function `f` on `n` bits,
```
sensitivity(f) >= sqrt(degree(f)).
```
So the more "global" the function's dependence on its inputs (high degree), the
more it must *respond* to single-bit changes somewhere (high sensitivity).

## Where GOAL appears in the repo

### LaTeX (lecture notes)
The main theorem near the end of `sensitivity-polynomial.tex` states the same fact:
```tex
\begin{theorem}
  s(f) \ge \sqrt{\deg(f)}.
\end{theorem}
```

### Lean (formalization)
The final theorem in `sensitivity.lean` is:
```lean
/-
A boolean function of degree n has sensitivity at least sqrt(n).
-/
theorem sensitivity_conjecture {n : ℕ} (f : (Fin n → Bool) → Bool) :
  (sensitivity f : ℝ) ≥ Real.sqrt (degree f) := by
    cases eq_or_ne ( degree f ) 0 <;> simp_all +decide;
    -- Let k = degree f. There exists a set S with |S| = k and f_hat(S) ≠ 0.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = degree f ∧ ∃ S : Finset (Fin n), S.card = k ∧ fourier_coeff f S ≠ 0 := by
      unfold degree at *;
      -- Since the set of S where fourier_coeff f S is non-zero is finite, it must have a maximum element in terms of cardinality.
      obtain ⟨S, hS⟩ : ∃ S : Finset (Fin n), fourier_coeff f S ≠ 0 ∧ ∀ T : Finset (Fin n), fourier_coeff f T ≠ 0 → T.card ≤ S.card := by
        have h_finite : Set.Finite {S : Finset (Fin n) | fourier_coeff f S ≠ 0} := by
          exact Set.toFinite _;
        apply_rules [ Set.exists_max_image ];
        contrapose! h_finite; aesop;
      refine' ⟨ _, rfl, S, _, hS.1 ⟩;
      refine' le_antisymm _ _;
      · exact Finset.le_sup ( f := Finset.card ) ( by aesop );
      · aesop;
    -- By `exists_restriction_fourier_coeff_univ_ne_zero`, there exists z such that the restriction g = restriction f S z has g_hat(univ) ≠ 0.
    obtain ⟨S, hS_card, hS_fourier⟩ := hk.2
    obtain ⟨z, hz⟩ : ∃ z : Fin n → Bool, fourier_coeff (restriction f S z) Finset.univ ≠ 0 := by
      exact exists_restriction_fourier_coeff_univ_ne_zero f S hS_fourier
    -- By `degree_eq_n_of_fourier_coeff_univ_ne_zero`, degree g = k.
    have h_deg_g : degree (restriction f S z) = S.card := by
      have := degree_eq_n_of_fourier_coeff_univ_ne_zero ( restriction f S z ) hz; aesop;
    -- By `sensitivity_ge_sqrt_degree_of_degree_eq_n`, sensitivity g ≥ √k.
    have h_sens_g : (sensitivity (restriction f S z) : ℝ) ≥ Real.sqrt (degree (restriction f S z)) := by
      have := sensitivity_ge_sqrt_degree_of_degree_eq_n ( restriction f S z ) ; aesop;
    -- By `sensitivity_restriction_le`, sensitivity f ≥ sensitivity g.
    have h_sens_f : (sensitivity f : ℝ) ≥ (sensitivity (restriction f S z) : ℝ) := by
      exact_mod_cast sensitivity_restriction_le f S z;
    grind
```
This is the GOAL atom in code form.

## How GOAL connects to neighboring concepts
GOAL is proved by composing two neighboring atoms:

1) **FULLCASE (degree = n)**
   If a function has full degree on `n` variables, then its sensitivity is at
   least `sqrt(n)`. This is the "hard core" proven using the Huang matrix,
   large level sets, and spectral bounds.

2) **REDUCE (general degree -> full degree)**
   For an arbitrary `f`, let `k = degree(f)`. The reduction shows that there is
   a restriction of `f` to a `k`-dimensional subcube that has full degree `k`.
   Sensitivity cannot increase under restriction, so a lower bound on the
   restricted function gives the same bound for the original one.

Put together, these two pieces give the final inequality for all functions.

## The reduction idea in plain language (REDUCE -> GOAL)
Restriction is "freezing" some inputs. If you freeze all but the variables in
some set `S`, you get a smaller function `g` that only depends on `|S|` inputs.
Two key facts make this work:

- If a Fourier coefficient `f_hat(S)` is nonzero, there is a restriction where the
  top coefficient of `g` (on all remaining variables) is nonzero.
- Sensitivity can only go *down* when you freeze variables.

So you pick a maximum-degree coefficient `S`, restrict to get a full-degree `g`,
apply FULLCASE to `g`, and lift the bound back to `f`.

Lean sketch (simplified):
```lean
/-
A boolean function of degree n has sensitivity at least sqrt(n).
-/
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

-- General case (GOAL)
theorem sensitivity_conjecture {n : ℕ} (f : (Fin n → Bool) → Bool) :
  (sensitivity f : ℝ) ≥ Real.sqrt (degree f) := by
    cases eq_or_ne ( degree f ) 0 <;> simp_all +decide;
    -- Let k = degree f. There exists a set S with |S| = k and f_hat(S) ≠ 0.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = degree f ∧ ∃ S : Finset (Fin n), S.card = k ∧ fourier_coeff f S ≠ 0 := by
      unfold degree at *;
      -- Since the set of S where fourier_coeff f S is non-zero is finite, it must have a maximum element in terms of cardinality.
      obtain ⟨S, hS⟩ : ∃ S : Finset (Fin n), fourier_coeff f S ≠ 0 ∧ ∀ T : Finset (Fin n), fourier_coeff f T ≠ 0 → T.card ≤ S.card := by
        have h_finite : Set.Finite {S : Finset (Fin n) | fourier_coeff f S ≠ 0} := by
          exact Set.toFinite _;
        apply_rules [ Set.exists_max_image ];
        contrapose! h_finite; aesop;
      refine' ⟨ _, rfl, S, _, hS.1 ⟩;
      refine' le_antisymm _ _;
      · exact Finset.le_sup ( f := Finset.card ) ( by aesop );
      · aesop;
    -- By `exists_restriction_fourier_coeff_univ_ne_zero`, there exists z such that the restriction g = restriction f S z has g_hat(univ) ≠ 0.
    obtain ⟨S, hS_card, hS_fourier⟩ := hk.2
    obtain ⟨z, hz⟩ : ∃ z : Fin n → Bool, fourier_coeff (restriction f S z) Finset.univ ≠ 0 := by
      exact exists_restriction_fourier_coeff_univ_ne_zero f S hS_fourier
    -- By `degree_eq_n_of_fourier_coeff_univ_ne_zero`, degree g = k.
    have h_deg_g : degree (restriction f S z) = S.card := by
      have := degree_eq_n_of_fourier_coeff_univ_ne_zero ( restriction f S z ) hz; aesop;
    -- By `sensitivity_ge_sqrt_degree_of_degree_eq_n`, sensitivity g ≥ √k.
    have h_sens_g : (sensitivity (restriction f S z) : ℝ) ≥ Real.sqrt (degree (restriction f S z)) := by
      have := sensitivity_ge_sqrt_degree_of_degree_eq_n ( restriction f S z ) ; aesop;
    -- By `sensitivity_restriction_le`, sensitivity f ≥ sensitivity g.
    have h_sens_f : (sensitivity f : ℝ) ≥ (sensitivity (restriction f S z) : ℝ) := by
      exact_mod_cast sensitivity_restriction_le f S z;
    grind
```

## Prerequisites and how to read GOAL
Minimal background concepts that GOAL relies on:
- **Sensitivity (SEN0):** maximum number of single-bit flips that change `f(x)`.
- **Fourier coefficient / degree (FOURIER0, DEG0):** degree is the size of the
  largest set `S` with `f_hat(S) != 0`.
- **Restriction machinery (RESTRICT0, SENS_MONO):** freezing variables can only
  decrease sensitivity.
- **FULLCASE:** the heavy spectral argument for the full-degree case.

If you are not comfortable with Fourier language, it is enough to remember:
degree measures the largest number of bits that ever act *together* in the function,
and GOAL says that forces noticeable single-bit sensitivity somewhere.

## Takeaway
GOAL is the proof's destination: the Sensitivity Conjecture inequality
`sensitivity(f) >= sqrt(degree(f))`. It is not proven directly, but by reducing
the general case to the full-degree case and importing the spectral bound from
FULLCASE. Once those two neighboring atoms are in place, GOAL is the final
assembly step.
