# INTERLACE

## Atom summary (from breakdown.md)
- Represents: principal-submatrix interlacing, specialized to a single inequality: `lambda_max(A[S]) >= lambda_{|S|-1}(A)`.
- Depends on: RAYLEIGH (Rayleigh quotient toolkit, including the support/zero-padding relation) and MINMAX (Courant-Fischer min-max principle).
- Used by: HUANG_SUB_LOWER (to force a large eigenvalue for a large subset `S`).

## Intuition and motivation
In the proof, we build a special matrix `A_n` whose eigenvalues we understand exactly. We then look at a subset `S` of vertices of the hypercube (coming from the level set of a transformed Boolean function) and take the principal submatrix `A_n[S]` that keeps only rows/columns indexed by `S`. To connect the global spectrum of `A_n` to this smaller matrix, we need a guarantee that a large enough submatrix still "inherits" a large eigenvalue. That is what interlacing provides.

Think of eigenvalues as "resonant frequencies" of a system. If you remove some coordinates (like muting some strings on a guitar), you get a smaller system. Interlacing says the new frequencies cannot all slide past the old ones; they must sit between them. So the top frequency of the smaller system cannot drop below the appropriate high-ranked frequency of the original system. This is the exact lower bound we need before comparing against graph degrees.

## Plain-language statement
Let `A` be a real symmetric matrix, and let `A[S]` be the principal submatrix you get by restricting to rows and columns indexed by `S`. Suppose `|S| = m`, and list the eigenvalues of `A` in increasing order:

```
lambda_0(A) <= lambda_1(A) <= ... <= lambda_{n-1}(A).
```

Then the largest eigenvalue of `A[S]` is at least the `m`-th smallest eigenvalue of `A`:

```
lambda_max(A[S]) >= lambda_{m-1}(A).
```

This is the specific interlacing inequality used in the proof.

## How the proof works (sketch)
The result is a direct consequence of the min-max characterization of eigenvalues plus a Rayleigh-quotient comparison between `A` and `A[S]`.

1) Rayleigh quotient. For a nonzero vector `x`, define

```
R_A(x) = <A x, x> / <x, x>.
```

2) Min-max (Courant-Fischer). The `k`-th smallest eigenvalue can be written as:

```
lambda_k(A) = max_{dim C = k+1}  min_{x in C, x != 0} R_A(x).
```

3) Choose the right subspace. Let `V` be the subspace of vectors supported only on `S`. Then `dim V = m`.

4) Compare Rayleigh quotients. If `x` is supported on `S`, the Rayleigh quotient for `A` equals the Rayleigh quotient for the principal submatrix after reindexing:

```
R_A(x) = R_{A[S]}(y),
```

for the corresponding vector `y` in `R^m`. This is the "zero-padding" idea from RAYLEIGH.

5) Put it together. Min-max gives:

```
lambda_{m-1}(A) <= sup_{x in V, x != 0} R_A(x).
```

But the right-hand side is at most `lambda_max(A[S])` because the largest eigenvalue bounds all Rayleigh quotients of `A[S]`. Therefore,

```
lambda_max(A[S]) >= lambda_{m-1}(A).
```

## Connection to neighboring concepts in the proof
- RAYLEIGH supplies the key equivalence that vectors supported on `S` give the same Rayleigh quotient in `A` and `A[S]`.
- MINMAX provides the formula that turns that Rayleigh-quotient comparison into a statement about eigenvalues.
- HUANG_SUB_LOWER uses this inequality with Huang's explicit eigenvalues: since half of `A_n`'s eigenvalues are `-sqrt(n)` and half are `+sqrt(n)`, any `S` with `|S| > 2^{n-1}` forces `lambda_max(A_n[S]) >= sqrt(n)`.
- That lower bound later meets the spectral upper bound (from the graph degree side) to give the sensitivity bound.

## Relevant snippets
From the LaTeX notes ("Cauchy interlace" section), the classic interlacing statement (increasing order):

```tex
Given an n x (n-1) orthogonal projection matrix P, let B := P A P^*.
Let alpha_i, beta_i be the eigenvalues of A, B in increasing order.
alpha_i <= beta_i <= alpha_{i+1}.
```

From the Lean formalization (`eigenvalue_interlacing_max`):

```lean
lemma eigenvalue_interlacing_max {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (S : Finset (Fin n)) (hS : S.Nonempty) :
  let m := S.card
  let subA := principal_submatrix_fin A S
  let h_subA := principal_submatrix_fin_isSymm A hA S
  let evs_A := sorted_eigenvalues A hA
  let evs_sub := sorted_eigenvalues subA h_subA
  evs_sub.getLast (List.ne_nil_of_length_pos (by
  rw [ sorted_eigenvalues_length ] ; aesop)) ≥ evs_A.get ⟨m - 1, by
    rw [ sorted_eigenvalues_length ];
    exact lt_of_lt_of_le ( Nat.sub_lt ( Finset.card_pos.mpr hS ) zero_lt_one ) ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )⟩ := by
    classical
    -- Let $V$ be the subspace of vectors supported on $S$. Its dimension is $m$.
    set V := subspace_of_support S;
    -- By the Min-Max principle, the $(m-1)$-th eigenvalue of $A$ is $\le \sup_{x \in V, x \ne 0} R_A(x)$.
    have h_min_max : (sorted_eigenvalues A hA).get ⟨S.card - 1, by
        rw [ sorted_eigenvalues_length ];
        exact lt_of_lt_of_le ( Nat.sub_lt ( Finset.card_pos.mpr hS ) zero_lt_one ) ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )⟩ ≤
        ⨆ (x : {x : V // x.1 ≠ 0}), rayleigh_quotient A x.1 := by
      apply le_sup_rayleigh_of_dim_eq_succ A hA ⟨S.card - 1, by
        exact lt_of_lt_of_le ( Nat.sub_lt ( Finset.card_pos.mpr hS ) zero_lt_one ) ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )⟩ V
      rw [ Nat.sub_add_cancel ( Finset.card_pos.mpr hS ) ] ; exact subspace_of_support_dim S;
    -- For any $x \in V$, let $y$ be the corresponding vector in $\mathbb{R}^m$. Then $R_A(x) = R_{subA}(y)$.
    have h_rayleigh_eq : ∀ x ∈ V, x ≠ 0 → ∃ y : Fin (Fintype.card {x // x ∈ S}) → ℝ, y ≠ 0 ∧ rayleigh_quotient A x = rayleigh_quotient (principal_submatrix_fin A S) y := by
      intro x hx hx_ne_zero
      obtain ⟨y, hy⟩ : ∃ y : Fin (Fintype.card {x // x ∈ S}) → ℝ, x = fun i => if h : i ∈ S then y (Fintype.equivFin {x // x ∈ S} ⟨i, h⟩) else 0 := by
        have h_span : ∀ x ∈ V, ∃ y : {x // x ∈ S} → ℝ, x = fun i => if h : i ∈ S then y ⟨i, h⟩ else 0 := by
          intro x hx
          obtain ⟨y, hy⟩ : ∃ y : {x // x ∈ S} → ℝ, x = ∑ i : {x // x ∈ S}, y i • (Pi.single (i : Fin n) 1 : Fin n → ℝ) := by
            have h_span : x ∈ Submodule.span ℝ (Set.range (fun i : {x // x ∈ S} => (Pi.single (i : Fin n) 1 : Fin n → ℝ))) := by
              exact hx;
            rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_span;
            obtain ⟨ c, rfl ⟩ := h_span; use fun i => c i; simp +decide [ Finsupp.sum_fintype ] ;
          use y; ext i; simp [hy];
          split_ifs <;> simp_all +decide [ Pi.single_apply ];
          · rw [ Finset.sum_eq_single ⟨ i, by assumption ⟩ ] <;> aesop;
          · exact Finset.sum_eq_zero fun x hx => if_neg <| by aesop;
        obtain ⟨ y, rfl ⟩ := h_span x hx;
        exact ⟨ fun i => y ( Fintype.equivFin { x // x ∈ S } |>.symm i ), by ext i; aesop ⟩;
      refine' ⟨ y, _, _ ⟩;
      · contrapose! hx_ne_zero; aesop;
      · unfold rayleigh_quotient;
        unfold principal_submatrix_fin;
        unfold principal_submatrix; simp +decide [ hy, Matrix.mulVec, dotProduct ] ;
        congr! 1;
        · rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
          · refine' Finset.sum_bij ( fun i hi => Fintype.equivFin { x // x ∈ S } ⟨ i, hi ⟩ ) _ _ _ _ <;> simp +decide;
            · exact fun b => ⟨ _, Finset.mem_coe.mp ( Fintype.equivFin { x // x ∈ S } |>.symm b |>.2 ), by simp +decide ⟩;
            · intro a ha; simp +decide [ ha ] ;
              rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
              · rw [ ← Finset.sum_coe_sort ];
                refine' Or.inl ( Finset.sum_bij ( fun i hi => Fintype.equivFin { x // x ∈ S } ⟨ i, by aesop ⟩ ) _ _ _ _ ) <;> simp +decide;
                exact fun b => ⟨ _, Finset.mem_coe.mp ( Fintype.equivFin { x // x ∈ S } |>.symm b |>.2 ), by simp +decide ⟩;
              · aesop;
          · aesop;
        · rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
          · refine' Finset.sum_bij ( fun i hi => Fintype.equivFin { x // x ∈ S } ⟨ i, hi ⟩ ) _ _ _ _ <;> simp +decide;
            · exact fun b => ⟨ _, Finset.mem_coe.mp ( Fintype.equivFin { x // x ∈ S } |>.symm b |>.2 ), by simp +decide ⟩;
            · aesop;
          · aesop;
    -- By `rayleigh_le_max_eigenvalue`, $R_{subA}(y) \le \lambda_{\max}(subA)$.
    have h_rayleigh_le_max : ∀ y : Fin (Fintype.card {x // x ∈ S}) → ℝ, y ≠ 0 →
        rayleigh_quotient (principal_submatrix_fin A S) y ≤
          (sorted_eigenvalues (principal_submatrix_fin A S) (principal_submatrix_fin_isSymm A hA S)).getLast
            (List.ne_nil_of_length_pos (by
              rw [ sorted_eigenvalues_length ];
              exact Fintype.card_pos_iff.mpr ⟨ ⟨ hS.choose, hS.choose_spec ⟩ ⟩ )) := by
      intros y hy_nonzero
      apply rayleigh_le_max_eigenvalue (principal_submatrix_fin A S) (principal_submatrix_fin_isSymm A hA S) y hy_nonzero;
      exact ne_of_gt ( Fintype.card_pos_iff.mpr ⟨ ⟨ hS.choose, hS.choose_spec ⟩ ⟩ );
    refine le_trans h_min_max ?_;
    convert ciSup_le _;
    · simp +zetaDelta at *;
      exact ⟨ _, Submodule.subset_span ⟨ ⟨ hS.choose, hS.choose_spec ⟩, rfl ⟩, ne_of_apply_ne ( fun x => x hS.choose ) ( by simp +decide ) ⟩;
    · grind
```

These are the formal versions of the same idea. The proof in Lean mirrors the Rayleigh + min-max sketch above.

## Prerequisites (minimal)
- What a principal submatrix is (SUBMAT): keep rows/cols indexed by `S`.
- What the Rayleigh quotient is and how it behaves under restriction (RAYLEIGH).
- The min-max (Courant-Fischer) characterization of eigenvalues (MINMAX).
