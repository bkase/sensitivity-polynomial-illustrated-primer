# HUANG_SPEC: the explicit spectrum of the Huang matrix

## Intuition and motivation (why we need this)

The proof eventually compares a **large induced subgraph** of the hypercube to a **principal submatrix** of a special matrix called the Huang matrix `A_n`. A general linear-algebra fact (interlacing) says: if you take a big enough principal submatrix, its largest eigenvalue is at least some eigenvalue of the full matrix.  

So the strategy is:

1. Build a big principal submatrix `A_n[S]` (from a big vertex set `S`).
2. Use interlacing to lower-bound `lambda_max(A_n[S])` by a *known* eigenvalue of `A_n`.
3. Use that lower bound to force a large graph degree, which then forces large sensitivity.

Step 2 is where **HUANG_SPEC** lives. It gives the *explicit eigenvalues of `A_n`*, so we know exactly what interlacing can give us.

## What HUANG_SPEC represents (from `history/breakdown.md`)

- **Atom meaning:** The explicit spectrum of the reindexed Huang matrix `A_n_fin`:  
  *half the eigenvalues are `-sqrt(n)` and half are `+sqrt(n)`*.
- **Depends on:** **HUANG_PROP** (key algebraic properties like symmetry, `A_n^2 = n I`, and `trace(A_n) = 0`).
- **Used by:** **HUANG_SUB_LOWER** (interlacing lower bound for large principal submatrices).

## The key object: the Huang matrix `A_n`

In the notes, `A_n` is defined recursively (block matrix form):

```tex
A_1 = B_1 :=
  \begin{pmatrix}
  0 & 1 \\
  1 & 0
  \end{pmatrix}
,\quad
A_{n+1} :=
  \begin{pmatrix}
  A_n & I_{2^n} \\
  I_{2^n} & -A_n
  \end{pmatrix}
```

Think of this as a **signed adjacency matrix** of the hypercube: it is very close to the usual adjacency matrix, but some entries have their signs flipped in a structured way. This "signing" makes the spectrum clean and computable.

## What "spectrum" means, in plain language

An eigenvalue is a number `lambda` for which there is a nonzero vector `v` such that:

```
A v = lambda v
```

So the matrix acts like a **pure scaling** on that direction. The **spectrum** is just the list of all such scaling factors (counting multiplicity).  

Analogy: imagine `A` as a machine that stretches or flips vectors. The eigenvalues tell you all the "pure stretch" factors the machine can produce, and how many independent directions get each stretch.

## The HUANG_SPEC statement (math idea)

From the notes:

> Half the eigenvalues of `A_n` are `sqrt(n)` and half are `-sqrt(n)`.

Why is this true?

1. **`A_n^2 = n I`.**  
   If `A v = lambda v`, then applying `A` twice gives `A^2 v = lambda^2 v`.  
   But `A^2 = n I`, so `A^2 v = n v`.  
   Therefore `lambda^2 = n`, so every eigenvalue is either `+sqrt(n)` or `-sqrt(n)`.

2. **`trace(A_n) = 0`.**  
   For symmetric matrices, the trace equals the sum of eigenvalues.  
   If the only possible values are `+sqrt(n)` and `-sqrt(n)` and the sum is `0`, then the counts must be equal.

3. **Matrix size is `2^n`.**  
   So there are `2^n` eigenvalues total, giving `2^(n-1)` of each sign.

That is the full spectral description.

## How this looks in Lean (formal statement)

Here is the Lean statement that formalizes HUANG_SPEC:

```lean
/-
The sorted eigenvalues of the Huang matrix A_n (for n > 0) are 2^(n-1) copies of -sqrt(n) and 2^(n-1) copies of sqrt(n).
-/
theorem huang_eigenvalues_eq_list (n : ℕ) (hn : n ≠ 0) :
  let evs := sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)
  evs = List.replicate (2^(n-1)) (-Real.sqrt n) ++ List.replicate (2^(n-1)) (Real.sqrt n) := by
    induction' n with n ih;
    · contradiction;
    · convert huang_eigenvalues_eq_list_succ n using 1;
      norm_cast
```

What this means (in plain terms):

- `huang_matrix_fin n` is the reindexed Huang matrix (same matrix, but indexed by `Fin (2^n)`).
- `sorted_eigenvalues` produces its eigenvalues in sorted order.
- That list is exactly:
  - `2^(n-1)` copies of `-sqrt(n)`, then
  - `2^(n-1)` copies of `+sqrt(n)`.

This is the formal version of "half negative, half positive."

## How HUANG_SPEC connects to neighboring concepts

**Upstream (prerequisites):**

- **HUANG_DEF** defines `A_n` recursively.
- **HUANG_PROP** proves:
  - `A_n` is symmetric (so real eigenvalues exist),
  - `A_n^2 = n I` (so eigenvalues have magnitude `sqrt(n)`),
  - `trace(A_n) = 0` (so the `+` and `-` counts match).

**Downstream (what uses it):**

- **HUANG_SUB_LOWER** uses interlacing.  
  If a principal submatrix has size `> 2^(n-1)`, interlacing says its largest eigenvalue is at least the `2^(n-1)`-th eigenvalue of `A_n`.  
  HUANG_SPEC says that eigenvalue is exactly `+sqrt(n)`.

This is the crucial lower bound that later becomes a **degree bound** and finally a **sensitivity bound**.

## Why this matters in the proof

HUANG_SPEC is the moment where the proof gets a **hard numeric value** (`sqrt(n)`) out of the Huang matrix. Without it, interlacing only says "some eigenvalue of `A_n`," which is too vague to force a strong lower bound on sensitivity. HUANG_SPEC turns the abstract spectral step into a concrete inequality.

## Minimal prerequisites (no formal math needed)

To follow HUANG_SPEC, you only need:

- The idea of a **matrix** as a linear "machine".
- The idea of an **eigenvalue** as a scaling factor on a special direction.
- The facts that:
  - `A^2 = n I` forces eigenvalues to have magnitude `sqrt(n)`.
  - `trace(A) = sum of eigenvalues` (for symmetric matrices).

Everything else (hypercube, induced subgraphs, sensitivity) comes after this piece.
