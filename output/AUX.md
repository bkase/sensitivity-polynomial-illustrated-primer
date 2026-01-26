# AUX

## Atom summary (from breakdown.md)
- Represents: auxiliary alternative definitions in the Lean file (charpoly-sorted eigenvalues, an interlacing predicate, min-max eigenvalue definitions, and Courant-Fischer inf/sup variants).
- Depends on: INF_LEAN (Lean scaffolding: imports, options, and tactics that make these definitions typecheck).
- Used by: no downstream atoms in this repo; these definitions are not used in the final proof.

## Intuition and motivation (why do we need this?)
The proof of the Sensitivity Conjecture needs spectral facts about matrices, like interlacing and min-max characterizations of eigenvalues. The main proof uses one particular set of definitions for eigenvalues and Rayleigh quotients, but there are multiple equivalent ways to formalize these ideas in Lean.

AUX is a small toolbox of alternate interfaces:
- ways to list eigenvalues by sorting the roots of the characteristic polynomial,
- a list-based definition of interlacing (the "between" relation on two sorted lists),
- explicit min-max and inf-sup formulas that match the classic Courant-Fischer statements.

Think of AUX as a set of spare parts: not required to build the final machine, but useful for cross-checking ideas or proving the same results in a different style.

## Plain-language explanation (with analogy)
Eigenvalues can be listed in many equivalent ways. Imagine you have a set of "vibration frequencies" for a system. You can:
- compute a polynomial whose roots are those frequencies, then sort the roots, or
- compute them as outcomes of a min-max game (pick a subspace, then an adversary picks a worst-case direction).

Interlacing is the idea that when you cut the system down to a smaller one (a principal submatrix), the new frequencies cannot all jump to one side; they must sit between the old ones. If you line up two sorted lists, each entry of the smaller list fits between two consecutive entries of the larger list.

AUX formalizes these ideas as definitions. It does not prove new theorems itself; it just gives these concepts explicit names in Lean.

## What is actually defined in AUX (Lean snippets)
These are taken directly from `sensitivity.lean`.

1) Sorted eigenvalues from the characteristic polynomial:

```lean
/-
The sorted list of eigenvalues of a real matrix, defined as the sorted roots of its characteristic polynomial.
-/
noncomputable def sorted_eigenvalues_list {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : List ℝ :=
  (A.charpoly.roots).sort (· ≤ ·)
```

This says: take the characteristic polynomial of `A`, find its roots, and sort them into a list.

2) A list-based interlacing predicate:

```lean
/-
A predicate asserting that list M interlaces list L.
-/
def interlacing (L M : List ℝ) : Prop :=
  L.length = M.length + 1 ∧
  ∀ i : Fin M.length, L[i]! ≤ M[i]! ∧ M[i]! ≤ L[i.1 + 1]!
```

This encodes the statement: every entry of the smaller list `M` sits between two consecutive entries of the larger list `L`.

3) A helper theorem connecting symmetric and Hermitian matrices:

```lean
/-
A real matrix is symmetric if and only if it is Hermitian.
-/
theorem isSymm_iff_isHermitian_real {n : Type*} [Fintype n] (A : Matrix n n ℝ) :
  A.IsSymm ↔ A.IsHermitian := by
  rw [Matrix.IsSymm, Matrix.IsHermitian, Matrix.conjTranspose, Matrix.transpose]
  simp
  rfl
```

This bridge lemma lets us use Mathlib's Hermitian eigenvalue machinery for real symmetric matrices.

4) The sorted eigenvalues of a symmetric matrix (using Hermitian eigenvalues):

```lean
/-
The sorted eigenvalues of a symmetric matrix.
-/
noncomputable def sorted_eigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) : List ℝ :=
  let hA' : A.IsHermitian := (isSymm_iff_isHermitian_real A).mp hA
  (List.ofFn (hA'.eigenvalues)).mergeSort (· ≤ ·)
```

5) A symmetry lemma for the dot product with matrix-vector multiplication:

```lean
/-
For a symmetric matrix A, <Ax, y> = <x, Ay>.
-/
theorem dotProduct_mulVec_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (x y : Fin n → ℝ) :
  dotProduct (A.mulVec x) y = dotProduct x (A.mulVec y) := by
    simp +decide [ Matrix.mulVec, dotProduct, mul_comm ];
    simp +decide only [Finset.mul_sum _ _ _, mul_left_comm, mul_comm];
    rw [ Finset.sum_comm ];
    conv_rhs => rw [ ← hA ] ;
    rfl
```

This says that for symmetric matrices, you can move the matrix from one side of the dot product to the other.

6) A max-min eigenvalue functional:

```lean
/-
The max-min value for the k-th eigenvalue.
-/
def min_max_eigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ⨆ (C : Submodule ℝ (Fin n → ℝ)) (_ : Module.finrank ℝ C = k + 1),
    ⨅ (x : {x : C // dotProduct (x : Fin n → ℝ) (x : Fin n → ℝ) = 1}),
      dotProduct (A.mulVec (x : Fin n → ℝ)) (x : Fin n → ℝ)
```

This is the Courant-Fischer "max-min" formula: pick a (k+1)-dimensional subspace `C`, then take the worst unit vector in `C`, and finally choose the best such subspace.

7) An inf-sup (dual) Courant-Fischer functional:

```lean
/-
The Courant-Fischer Min-Max value (Inf-Sup) for the k-th eigenvalue.
-/
def courant_fischer_inf_sup {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : ℝ :=
  ⨅ (V : Submodule ℝ (Fin n → ℝ)) (_ : Module.finrank ℝ V = k + 1),
    ⨆ (x : {x : V // x.1 ≠ 0}), rayleigh_quotient A x.1
```

This is the "inf-sup" variant: first choose a subspace, then take the best Rayleigh quotient inside it.

## How AUX connects to neighboring concepts in the proof
Even though AUX is not used by the final proof, it mirrors the concepts in the main spectral chain:

- The LaTeX notes' "Cauchy interlace" section states the min-max formula and interlacing inequalities. AUX provides matching Lean definitions for those ideas.
- The actual Lean proof uses a different eigenvalue list (`sorted_eigenvalues` based on Hermitian eigenvalues) plus the Rayleigh quotient toolkit (RAYLEIGH) and Courant-Fischer principle (MINMAX) to derive interlacing (INTERLACE).
- You can think of AUX as a parallel route: if one wanted to re-prove interlacing using characteristic-polynomial roots and the `interlacing` predicate, these definitions would be the starting point.

So AUX sits next to MINMAX and INTERLACE in concept, but it does not feed into them in the repo's dependency graph.

## Relevant math snippet from the LaTeX notes
The notes state the classic min-max formula:

```tex
lambda_k = max_C min_{||x|| = 1, x in C} <Ax, x>
```

AUX's `min_max_eigenvalue` is the formal Lean equivalent of this statement, encoded as a supremum over subspaces followed by an infimum over unit vectors.

## Prerequisites (minimal)
To follow AUX you only need:
- the idea of eigenvalues and the characteristic polynomial,
- what a subspace is and what its dimension means,
- the Rayleigh quotient and why it measures "stretch" by a matrix.

If you have seen the Cauchy interlacing statement and Courant-Fischer min-max principle (from the LaTeX notes), AUX is just those concepts spelled out as definitions.
