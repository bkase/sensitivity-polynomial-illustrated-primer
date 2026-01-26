# RAYLEIGH

## Intuition and motivation

In the proof, we need to compare eigenvalues of a big symmetric matrix A with eigenvalues of a smaller matrix made by keeping only the rows/columns indexed by a subset S (a principal submatrix, from the SUBMAT atom). The key bridge is the **Rayleigh quotient**:

- It turns a vector x into a number that measures how much A "stretches" x.
- For symmetric matrices, this number always lives between the smallest and largest eigenvalues.
- If we restrict vectors to a subspace (for example, vectors supported only on S), Rayleigh quotients let us compare A to A[S] by simple zero-padding.

This toolkit is the engine that powers the **min-max principle (MINMAX)** and the **interlacing inequality (INTERLACE)**. Without it, we cannot move between the full matrix and the submatrix in a clean, quantitative way.

## What the Rayleigh quotient is (plain language)

Given a nonzero vector x and a symmetric matrix A, the Rayleigh quotient is

```
R_A(x) = <x, A x> / <x, x>
```

Think of it like this:

- The denominator <x, x> is the "size" of x (its squared length).
- The numerator <x, A x> is the "energy" of x after A acts on it.
- So R_A(x) is the average amount of stretching A applies in the direction of x.

Analogy: imagine A is a system of springs, and x is a displacement. Then <x, A x> is the energy stored in the springs. Dividing by <x, x> normalizes by how large the displacement is. The Rayleigh quotient is the energy per unit displacement.

For symmetric A, the Rayleigh quotient always lies between the smallest and largest eigenvalues. The maximum Rayleigh quotient is achieved exactly by the top eigenvector. This is the intuition behind the min-max principle used later.

## The core toolkit pieces in this proof

### 1) Definition (Lean)

In `sensitivity.lean`, the Rayleigh quotient is defined as:

```lean
def rayleigh_quotient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (A.mulVec x) / dotProduct x x
```

This is the formal version of R_A(x) = <x, Ax> / <x, x>. The function takes a symmetric matrix A indexed by `Fin n` and a vector x (represented as a function from `Fin n` to the reals), and returns the quotient of the dot product of x with Ax divided by the dot product of x with itself.

### 2) Reindexing invariance

When we rename or reindex coordinates, the Rayleigh quotient does not change. This matters because submatrices are often presented with different index types (like `Fin n` vs. `Fin |S|`). The Lean lemma is:

```lean
lemma rayleigh_quotient_reindex {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin n ≃ Fin m) (x : Fin n → ℝ) :
  rayleigh_quotient A x = rayleigh_quotient (Matrix.reindex e e A) (x ∘ e.symm) := by
    unfold rayleigh_quotient;
    simp +decide [ Matrix.mulVec, dotProduct ];
    simp +decide only [← Equiv.sum_comp e];
    simp +decide
```

Interpretation: if you just relabel coordinates via an equivalence `e : Fin n ≃ Fin m`, the Rayleigh quotient stays the same. The reindexed matrix uses `Matrix.reindex e e A`, and the vector is composed with `e.symm` to account for the coordinate change.

### 3) Zero-padding to compare A and A[S]

This is the key bridge to principal submatrices. Suppose y is a vector only living on the indices in S. Create a full-length vector x by **zero-padding** outside S:

```
for i in [1..n]:
  x_i = y_i if i in S
  x_i = 0   if i not in S
```

Then the Rayleigh quotient of x for the full matrix A equals the Rayleigh quotient of y for the submatrix A[S]. In Lean this is:

```lean
lemma rayleigh_quotient_submatrix_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
  (equiv : {x // x ∈ S} ≃ Fin S.card)
  (y : Fin S.card → ℝ) :
  let x : Fin n → ℝ := fun i => if h : i ∈ S then y (equiv ⟨i, h⟩) else 0
  rayleigh_quotient A x = rayleigh_quotient (Matrix.reindex equiv equiv (A.submatrix Subtype.val Subtype.val)) y
```

Plain language: if a vector lives only on S (with zeros elsewhere), you can treat it either as a vector in the big space or as a vector in the small space, and the Rayleigh quotient is the same. The `equiv` provides a bijection between elements of S and `Fin S.card`, allowing us to reindex the submatrix. The vector x is defined using a dependent if: when `i ∈ S`, it takes the value `y (equiv ⟨i, h⟩)`; otherwise it is 0.

### 4) Rayleigh quotient is bounded by the top eigenvalue

Another useful fact in the toolkit (still in the Rayleigh family) is that for symmetric A and any nonzero x,

```
R_A(x) <= lambda_max(A)
```

This is formalized as `rayleigh_le_max_eigenvalue` in `sensitivity.lean`. It lets us turn Rayleigh-quotient estimates into eigenvalue bounds.

## How this connects to neighboring atoms in the proof

From `history/breakdown.md`, the dependencies are:

- **Depends on:** SUBMAT (principal submatrix construction).
- **Used by:** MINMAX (Courant-Fischer) and INTERLACE (principal-submatrix interlacing).

Here is the flow in plain terms:

1) **SUBMAT** defines A[S].
2) **RAYLEIGH** gives the tool to compare Rayleigh quotients of A and A[S] via zero-padding.
3) **MINMAX** uses Rayleigh quotients to express eigenvalues as max/min over subspaces.
4) **INTERLACE** applies MINMAX to the subspace of vectors supported on S, producing
   the interlacing inequality: the largest eigenvalue of A[S] is at least the |S|-th
   smallest eigenvalue of A.
5) **HUANG_SUB_LOWER** then plugs in the explicit eigenvalues of the Huang matrix.

So RAYLEIGH is the "transport mechanism" that lets you carry Rayleigh-quotient estimates between the big matrix and the submatrix.

## Connection to the LaTeX notes

The LaTeX notes do not name the Rayleigh quotient explicitly, but it appears in the Cauchy interlacing section. For example, the min-max formula there is:

```tex
lambda_k = max_C min_{||x|| = 1, x in C} <A x, x>
```

This is exactly the Rayleigh quotient, except with x normalized to have norm 1 (so the denominator is 1). The Rayleigh quotient is the reason this formula works: it turns eigenvalue questions into optimization problems over vectors and subspaces.

## Quick mental model

- Rayleigh quotient = "average stretch" of A in direction x.
- Symmetric A => Rayleigh quotient lives between the smallest and largest eigenvalues.
- Zero-padding = a way to treat vectors on S as vectors in the full space without changing their Rayleigh quotient.

This makes RAYLEIGH the right tool to compare eigenvalues of A and A[S], and to prepare for min-max and interlacing in the next atoms.

## Prerequisites (lightweight)

- What a symmetric matrix is and why it has real eigenvalues.
- The principal submatrix operation (SUBMAT).
- Inner product notation <x, y> and the idea of vector length.

That is all you need to read MINMAX and INTERLACE next.
