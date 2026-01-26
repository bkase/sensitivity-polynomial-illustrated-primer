# REDUCE: general degree to full degree via restriction

## Intuition and motivation

The full-degree case (FULLCASE) is the hard core of the proof: if a Boolean
function has degree n, then its sensitivity is at least sqrt(n). But real
functions can have degree smaller than n. The REDUCE step is the bridge from
"any degree" to "full degree." It says: if f only depends on some subset of
coordinates in a high-degree way, then we can freeze all other coordinates and
focus on the subcube where f becomes full degree. Prove the bound there, then
lift it back to the original f.

Analogy: Imagine a huge control panel with n switches. The function f reacts
strongly only to a subset of switches. REDUCE is the act of taping down the
irrelevant switches and zooming in on the important ones. If the restricted
panel is already hard to tame (high sensitivity), then the full panel cannot be
any easier.

## What REDUCE represents (from breakdown.md)

REDUCE is the single strategy statement:

"Reduce the general-degree case to the full-degree case by restricting f to a
subcube where the top Fourier coefficient is nonzero."

This is an atomic proof step in the breakdown graph even though it uses several
lemmas internally.

## Dependencies and dependents (from breakdown.md)

Direct dependencies (what REDUCE uses):
- FULLCASE: the full-degree theorem sensitivity(f) >= sqrt(n) when degree(f) = n.
- SENS_MONO: restricting a function cannot increase sensitivity.
- EXIST_TOP: if the average of top coefficients of restrictions is nonzero,
  some restriction has nonzero top coefficient.
- DEG_FROM_TOP: nonzero top Fourier coefficient implies full degree.

Direct dependents (what uses REDUCE):
- GOAL: the final theorem sensitivity(f) >= sqrt(degree(f)).

Note: REDUCE also relies on the restriction construction and the Fourier
averaging identity (RESTRICT0 and FOURIER_AVG), even though the breakdown graph
groups those under the lemmas above.

## Prerequisites in plain language

You only need a few concepts to follow REDUCE:

1) Sensitivity: at an input x, count how many single-bit flips change f(x).
   Sensitivity(f) is the maximum of that count over all x.

2) Fourier degree: expand f in the parity basis (chi_S). The degree is the
   largest size of a set S with nonzero Fourier coefficient f_hat(S).

3) Restriction: pick a subset S of coordinates and fix all others to a pattern
   z. The result is a new function on |S| bits.

## The reduction idea step by step

Let k = degree(f). The REDUCE proof is a short chain of ideas:

1) Pick a highest-degree set S (size k) with f_hat(S) != 0.
   This is the "degree witness" idea: the degree is achieved by some set S.

2) Restrict f to S by freezing all other coordinates to a pattern z. Call the
   restricted function g = f|_{S,z}. This is a function on k bits.

3) Averaging over restrictions:
   The Fourier coefficient f_hat(S) is the average, over all z, of the top
   Fourier coefficient of g. Formally:

   f_hat(S) = average_z ( (f|_{S,z})_hat(univ) )

   If f_hat(S) != 0, then this average is nonzero, so at least one z has
   (f|_{S,z})_hat(univ) != 0. (That is the EXIST_TOP step.)

4) Nonzero top coefficient means full degree:
   If (f|_{S,z})_hat(univ) != 0, then degree(f|_{S,z}) = |S| = k.
   (That is DEG_FROM_TOP.) So g has full degree in dimension k.

5) Apply FULLCASE to g:
   sensitivity(g) >= sqrt(k).

6) Lift back to f using SENS_MONO:
   Restricting cannot increase sensitivity, so sensitivity(g) <= sensitivity(f).
   Therefore sensitivity(f) >= sqrt(k) = sqrt(degree(f)).

That is exactly the general case of the Sensitivity Conjecture.

## Where this appears in the LaTeX notes

The LaTeX file says the same idea informally:

"It is also helpful to have deg(f) = n. To do this, pick a term T in f of
maximum degree and restrict to the subcube Q_T."

This sentence is the REDUCE step in one line: pick the top-degree term and
zoom into the subcube where it becomes full degree.

## Lean snippets that implement REDUCE

Restriction and monotonicity:
```lean
def restriction {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (z : Fin n → Bool) : (Fin (Fintype.card {x // x ∈ S}) → Bool) → Bool :=
  fun y =>
    let x : Fin n → Bool := fun i =>
      if h : i ∈ S then
        y (Fintype.equivFin {j // j ∈ S} ⟨i, h⟩)
      else
        z i
    f x

lemma sensitivity_restriction_le {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (z : Fin n → Bool) :
  sensitivity (restriction f S z) ≤ sensitivity f := by
    unfold sensitivity;
    simp +decide only [Finset.sup_le_iff];
    intro x;
    simp +decide [ restriction ];
    refine' le_trans _ ( Finset.le_sup <| Finset.mem_univ <| fun i => if h : i ∈ S then x ( Fintype.equivFin _ ⟨ i, h ⟩ ) else z i );
    refine' le_trans _ ( Finset.card_le_card _ );
    rotate_left;
    exact Finset.image ( fun y : Fin ( Fintype.card { x // x ∈ S }) → Bool => fun i => if h : i ∈ S then y ( Fintype.equivFin _ ⟨ i, h ⟩ ) else z i ) ( Finset.filter ( fun y => Finset.card ( Finset.filter ( fun i => ¬x i = y i ) Finset.univ ) = 1 ∧ ¬f ( fun i => if h : i ∈ S then x ( Fintype.equivFin _ ⟨ i, h ⟩ ) else z i ) = f ( fun i => if h : i ∈ S then y ( Fintype.equivFin _ ⟨ i, h ⟩ ) else z i ) ) ( Finset.univ : Finset ( Fin ( Fintype.card { x // x ∈ S }) → Bool ) ) );
    · simp +decide [ Finset.subset_iff ];
      rintro _ y hy₁ hy₂ rfl; simp_all +decide [ Finset.card_eq_one ] ;
      obtain ⟨ a, ha ⟩ := hy₁; use ( Fintype.equivFin { x // x ∈ S } ).symm a; ext i; by_cases hi : i ∈ S <;> simp_all +decide [ Finset.ext_iff ] ;
      · aesop;
      · intro H; have := ha a; simp_all +decide [ Fin.ext_iff ] ;
    · rw [ Finset.card_image_of_injective ];
      intro y₁ y₂ hy; ext i; replace hy := congr_fun hy ( Fintype.equivFin { x // x ∈ S } |>.symm i ) ; aesop;
```

Fourier averaging and existence of a good restriction:
```lean
lemma fourier_coeff_restriction_avg {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) :
  fourier_coeff f S = (Finset.sum Finset.univ (fun z => fourier_coeff (restriction f S z) Finset.univ)) / 2^n := by ...

lemma exists_restriction_fourier_coeff_univ_ne_zero {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (hS : fourier_coeff f S ≠ 0) :
  ∃ z : Fin n → Bool, fourier_coeff (restriction f S z) Finset.univ ≠ 0 := by
    rw [ fourier_coeff_restriction_avg ] at hS;
    exact not_forall.mp fun h => hS <| by rw [ Finset.sum_eq_zero fun _ _ => h _ ] ; norm_num;
```

Top coefficient implies full degree:
```lean
lemma degree_eq_n_of_fourier_coeff_univ_ne_zero {n : ℕ} (f : (Fin n → Bool) → Bool) (h : fourier_coeff f Finset.univ ≠ 0) :
  degree f = n := by
    refine' le_antisymm _ _;
    · exact Finset.sup_le fun S hS => Nat.le_trans ( Finset.card_le_univ _ ) ( by norm_num );
    · refine' le_trans _ ( Finset.le_sup <| Finset.mem_filter.mpr ⟨ Finset.mem_univ Finset.univ, h ⟩ );
      norm_num
```

Final reduction (the general theorem):
```lean
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

## How REDUCE connects to neighboring concepts

- It depends on FULLCASE because REDUCE ends by applying the full-degree
  theorem to the restricted function.
- It depends on restriction machinery (RESTRICT0, FOURIER_AVG, EXIST_TOP,
  DEG_FROM_TOP, SENS_MONO) to find the right subcube and lift the bound.
- It feeds GOAL, the final statement sensitivity(f) >= sqrt(degree(f)).

## Self-contained takeaway

REDUCE is the "zoom in" step. It turns a general-degree function into a
full-degree function by freezing irrelevant coordinates, uses the full-degree
bound on that smaller cube, and then lifts the result back. This is why the
proof can focus on the full-degree case without loss of generality.
