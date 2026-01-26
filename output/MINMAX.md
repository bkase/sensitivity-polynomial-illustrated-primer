# MINMAX (Courant-Fischer min-max principle)

## What this atom is in the repo
MINMAX is the Courant-Fischer min-max principle: a way to characterize the k-th eigenvalue of a symmetric matrix as an optimization problem over k-dimensional subspaces. In the proof, it is the bridge between the Rayleigh quotient (RAYLEIGH) and the interlacing inequality for principal submatrices (INTERLACE).

From `history/breakdown.md`:
- Represents: "Courant-Fischer / min-max principle giving eigenvalues as extrema over subspaces."
- Depends on: **RAYLEIGH** (Rayleigh quotient toolkit).
- Used by: **INTERLACE** (principal-submatrix interlacing) and **INF_TEX** (the LaTeX exposition).

## Intuition and motivation (why do we need this?)
Eigenvalues tell you how a matrix stretches space, but solving for them directly can be hard. The min-max principle says: you can *find* the k-th eigenvalue by playing a game with subspaces and vectors, using only the Rayleigh quotient (a "stretching score" for a vector). This is powerful because:
1) It lets you compare eigenvalues of a big matrix with eigenvalues of a smaller submatrix without computing them directly.
2) It turns spectral statements into optimization statements, which are easier to bound.

In this proof, we need to show that a large principal submatrix of the Huang matrix has a large eigenvalue. MINMAX makes that possible: once you can compare eigenvalues via subspaces, you can lower bound the submatrix's largest eigenvalue using the known spectrum of the full matrix.

## Plain-language explanation (with analogy)
Think of a symmetric matrix A as defining a "terrain height" for each direction x, given by the Rayleigh quotient:

```
R_A(x) = <Ax, x> / <x, x>
```

You can pick a k-dimensional subspace C (a flat k-dimensional "sheet" through the origin). Your opponent then picks the *worst* unit vector on that sheet, making the terrain height as small as possible. The min-max principle says:

> If you choose the best possible k-dimensional sheet, the height you can *guarantee* is exactly the k-th eigenvalue.

So MINMAX is like a guarantee game:
- You pick C to maximize the worst-case outcome.
- The opponent picks x in C to minimize the outcome.
- The value of this game is lambda_k.

This is the core reason we can turn "eigenvalue k" into "optimize Rayleigh quotient over subspaces."

## Formal statement (from the LaTeX notes)
In `sensitivity-polynomial.tex`, the lemma labeled `\ref{cauchy}` states:

```
lambda_k = max_C min_{||x|| = 1, x in C} <Ax, x>
```

where C ranges over all k-dimensional subspaces. For symmetric (or Hermitian) A, all eigenvalues are real, so this expression is well-defined. The notes also point out you can flip signs or swap min/max to get variants (e.g., the smallest eigenvalue).

## Lean definitions that encode the same idea
The Lean file defines a min-max functional directly:

```lean
def min_max_eigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ⨆ (C : Submodule ℝ (Fin n → ℝ)) (_ : Module.finrank ℝ C = k + 1),
    ⨅ (x : {x : C // dotProduct (x : Fin n → ℝ) (x : Fin n → ℝ) = 1}),
      dotProduct (A.mulVec (x : Fin n → ℝ)) (x : Fin n → ℝ)
```

There is also a Courant-Fischer version written as an inf-sup over Rayleigh quotients:

```lean
def courant_fischer_inf_sup {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : ℝ :=
  ⨅ (V : Submodule ℝ (Fin n → ℝ)) (_ : Module.finrank ℝ V = k + 1),
    ⨆ (x : {x : V // x.1 ≠ 0}), rayleigh_quotient A x.1
```

These are the formal counterparts of the same min-max idea used in the notes. The rest of the Lean development uses the Rayleigh quotient machinery and subspace dimension arguments to make the min-max step precise.

The key lemma that connects eigenvalues to the supremum of the Rayleigh quotient over subspaces is:

```lean
lemma le_sup_rayleigh_of_dim_eq_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (k : Fin n)
  (V : Submodule ℝ (Fin n → ℝ))
  (hV : Module.finrank ℝ V = k + 1) :
  (sorted_eigenvalues A hA).get ⟨k, by rw [sorted_eigenvalues_length]; exact k.isLt⟩ ≤ ⨆ (x : {x : V // x.1 ≠ 0}), rayleigh_quotient A x.1 := by
    -- Let U be the span of eigenvectors v_k, ..., v_{n-1}.
    set U : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ (Set.range (fun i : {j : Fin n // k ≤ j} => (Classical.choose (exists_orthonormal_basis_sorted A hA)) i));
    -- Since $V$ is $k+1$-dimensional and $U$ is $n-k$-dimensional, their intersection $U \cap V$ has dimension at least $1$.
    have h_inter : Module.finrank ℝ (↥(U ⊓ V)) ≥ 1 := by
      have h_inter : Module.finrank ℝ U = n - k := by
        rw [ @finrank_span_eq_card ];
        · rw [ Fintype.card_subtype ];
          rw [ show ( Finset.univ.filter fun x : Fin n => k ≤ x ) = Finset.Ici k by ext; simp +decide ] ; simp +decide;
        · refine' LinearIndependent.comp _ _ _;
          · exact ( Classical.choose ( exists_orthonormal_basis_sorted A hA ) ).orthonormal.linearIndependent;
          · exact Subtype.coe_injective;
      have h_inter : Module.finrank ℝ (↥(U ⊔ V)) ≤ n := by
        exact le_trans ( Submodule.finrank_le _ ) ( by simp );
      have := Submodule.finrank_sup_add_finrank_inf_eq U V;
      linarith [ Nat.sub_add_cancel ( show ( k : ℕ ) ≤ n from k.2.le ) ];
    -- Let $x$ be a nonzero vector in $U \cap V$.
    obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, x ≠ 0 ∧ x ∈ U ⊓ V := by
      contrapose! h_inter;
      rw [ show U ⊓ V = ⊥ from eq_bot_iff.mpr fun x hx => Classical.not_not.1 fun hx' => h_inter x hx' hx ] ; norm_num;
    refine' le_trans _ ( le_ciSup _ ⟨ ⟨ x, by aesop ⟩, by aesop ⟩ );
    · apply rayleigh_ge_of_mem_span_top A hA k (Classical.choose (exists_orthonormal_basis_sorted A hA)) (Classical.choose_spec (exists_orthonormal_basis_sorted A hA)) x;
      · exact hx.2.1;
      · exact hx.1;
    · refine' ⟨ ∑ i, ∑ j, |A i j|, Set.forall_mem_range.2 fun x => _ ⟩;
      refine' div_le_of_le_mul₀ _ _ _;
      · exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _;
      · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _;
      · -- By the properties of the dot product and the triangle inequality, we can bound the expression.
        have h_dot_product : ∀ (x : Fin n → ℝ), x ≠ 0 → |dotProduct x (A.mulVec x)| ≤ (∑ i, ∑ j, |A i j|) * dotProduct x x := by
          intros x hx_nonzero
          have h_dot_product : |dotProduct x (A.mulVec x)| ≤ ∑ i, ∑ j, |A i j| * |x i| * |x j| := by
            simp +decide [ dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_comm, mul_left_comm ];
            exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun j _ => by rw [ abs_mul, abs_mul ] );
          refine le_trans h_dot_product ?_;
          norm_num [ Finset.sum_mul _ _ _, mul_assoc, dotProduct ];
          exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ( by nlinarith only [ abs_mul_abs_self ( x i ), abs_mul_abs_self ( x j ), Finset.single_le_sum ( fun i _ => mul_self_nonneg ( x i ) ) ( Finset.mem_univ i ), Finset.single_le_sum ( fun i _ => mul_self_nonneg ( x i ) ) ( Finset.mem_univ j ) ] ) ( abs_nonneg _ );
        exact le_of_abs_le ( h_dot_product _ x.2 )
```

## How MINMAX connects to neighboring concepts in the proof
Here is the local chain in the proof:

1) **RAYLEIGH** defines the Rayleigh quotient and gives tools to compare it across vectors and subspaces.
2) **MINMAX** uses the Rayleigh quotient to characterize eigenvalues via subspaces.
3) **INTERLACE** applies MINMAX to principal submatrices: vectors supported on a subset S form a subspace, so the k-th eigenvalue of the full matrix bounds the largest eigenvalue of the submatrix.
4) **HUANG_SUB_LOWER** then plugs in the Huang matrix spectrum to get a concrete lower bound (sqrt(n)).

So MINMAX is the "hinge" that turns a global eigenvalue list into a lower bound on the spectral radius of a submatrix, which is exactly what the sensitivity proof needs.

## Prerequisites to keep in mind
If you are new to this, the concepts you need are:
- Eigenvalues and eigenvectors of a symmetric matrix (real eigenvalues, orthonormal eigenbasis).
- The Rayleigh quotient and its interpretation as a "stretching score."
- The idea of a k-dimensional subspace and its role as a set of allowed directions.

Once you have those, MINMAX is just a precise way of saying: "the k-th eigenvalue is the best worst-case Rayleigh quotient you can guarantee with a k-dimensional choice."
