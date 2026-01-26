# HUANG_PROP: Key properties of the Huang matrix (symmetry, square identity, trace)

## Intuition and motivation
The proof needs a matrix whose spectrum (its list of eigenvalues) is extremely clean. The hypercube adjacency matrix is the natural matrix, but its eigenvalues are messy to control in this argument. Huang's trick is to tweak signs in that adjacency matrix so that the new matrix A_n behaves like a "perfectly tuned" operator. The HUANG_PROP atom is the minimal package of facts that make that tuning obvious:

- A_n is symmetric (so its eigenvalues are real and well-behaved).
- A_n squared is exactly n times the identity (so every eigenvalue has square n).
- The trace is 0 (so the positive and negative eigenvalues cancel in sum).

Once you have these three facts, the spectrum is forced to be exactly half +sqrt(n) and half -sqrt(n). That clean spectrum is what powers the interlacing and graph-degree bounds later in the proof.

## What HUANG_PROP says in plain language
Think of A_n as a machine that takes a vector indexed by hypercube vertices and produces a new vector by mixing each vertex with its neighbors, but with carefully chosen plus/minus signs.

HUANG_PROP asserts three concrete, easy-to-test behaviors:

1) Symmetry: A_n is mirrored across its diagonal.
   - Analogy: the influence from u to v equals the influence from v to u.
   - Consequence: the matrix behaves like an undirected system, so eigenvalues are real and can be ordered.

2) Square identity: applying A_n twice is the same as multiplying by n.
   - Analogy: take a "signed step" to neighbors and then another signed step; all the cross-terms cancel, leaving you exactly n copies of the original vector.
   - Consequence: if A_n v = lambda v, then A_n^2 v = lambda^2 v = n v, so lambda^2 = n.

3) Trace zero: the sum of the diagonal entries of A_n is 0.
   - Analogy: the matrix has no "self-loop bias" overall.
   - Consequence: the sum of eigenvalues is 0, so the +sqrt(n) and -sqrt(n) eigenvalues appear in equal numbers.

These are the only invariants needed to pin down the spectrum in HUANG_SPEC.

## Where this shows up in the notes (TeX)
In `sensitivity-polynomial.tex`, the key spectral lemma is proved using exactly these properties:

```tex
By induction, A_n^2 = n I_{2^n} so every eigenvalue is +/- sqrt(n).
Furthermore, Tr(A_n) = 0 so there must be equal numbers of each.
```

That line is the HUANG_PROP content in the lecture notes: square identity plus trace zero. Symmetry is implicit from the block definition of A_n.

## How Lean encodes the same facts
The Lean file makes these properties explicit as separate theorems:

```lean
theorem huang_matrix_sq (n : ℕ) : (huang_matrix n) ^ 2 = (n : ℝ) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) := by
  induction' n with n ih;
  · norm_num [ sq ];
    exact mul_eq_zero_of_left rfl (huang_matrix 0)
  · -- By definition of huang_matrix, we have:
    have h_def : huang_matrix (n + 1) = Matrix.reindex (finSuccEquiv_huang_custom n).symm (finSuccEquiv_huang_custom n).symm (Matrix.fromBlocks (huang_matrix n) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (-huang_matrix n)) := by
      rfl;
    -- By definition of matrix multiplication and the induction hypothesis, we can expand the square of the block matrix.
    have h_expand : (Matrix.fromBlocks (huang_matrix n) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (-huang_matrix n)) ^ 2 = Matrix.fromBlocks ((n + 1 : ℝ) • 1) 0 0 ((n + 1 : ℝ) • 1) := by
      simp_all +decide [ sq, Matrix.fromBlocks_multiply ];
      norm_num [ add_smul, add_comm ];
    simp_all +decide [ sq, Matrix.reindex_apply ];
    ext i j; simp +decide [ Matrix.submatrix, Matrix.smul_eq_diagonal_mul ] ;
    by_cases hij : i = j <;> simp +decide [ hij, Matrix.one_apply ]

theorem huang_matrix_isSymm (n : ℕ) : (huang_matrix n).IsSymm := by
  induction' n with n ih;
  · exact rfl
  · -- By definition of huang_matrix, we know that huang_matrix (n + 1) is a block matrix with huang_matrix n on the diagonal, I on the off-diagonal, and -huang_matrix n on the other diagonal, reindexed to match the boolean hypercube indices.
    have h_block : huang_matrix (n + 1) = Matrix.reindex (finSuccEquiv_huang_custom n).symm (finSuccEquiv_huang_custom n).symm (Matrix.fromBlocks (huang_matrix n) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (-huang_matrix n)) := by
      rfl;
    simp_all +decide [ Matrix.IsSymm ];
    ext i j; simp +decide [ Matrix.fromBlocks_transpose, ih ] ;

theorem huang_matrix_trace (n : ℕ) : Matrix.trace (huang_matrix n) = 0 := by
  induction n <;> simp_all +decide [ Matrix.trace ];
  · rfl;
  · rename_i n ih; rw [ show ( huang_matrix ( n + 1 ) ) = Matrix.reindex ( finSuccEquiv_huang_custom n ).symm ( finSuccEquiv_huang_custom n ).symm ( Matrix.fromBlocks ( huang_matrix n ) ( 1 : Matrix _ _ ℝ ) ( 1 : Matrix _ _ ℝ ) ( -huang_matrix n ) ) by rfl ] ; simp +decide ;
    unfold finSuccEquiv_huang_custom;
    unfold finSuccEquiv_custom boolProdEquivSum_custom; simp +decide [ Matrix.fromBlocks ] ;
    rw [ show ( Finset.univ : Finset ( Fin ( n + 1 ) → Bool ) ) = Finset.image ( fun x : Fin n → Bool => Fin.cons true x ) Finset.univ ∪ Finset.image ( fun x : Fin n → Bool => Fin.cons false x ) Finset.univ from ?_, Finset.sum_union ] <;> norm_num [ Finset.sum_image, ih ];
    · rw [ neg_add_eq_zero ];
      exact rfl
    · norm_num [ Finset.disjoint_left ];
    · ext x; simp +decide ;
      exact if h : x 0 then Or.inl ⟨ fun i => x i.succ, by ext i; cases i using Fin.inductionOn <;> aesop ⟩ else Or.inr ⟨ fun i => x i.succ, by ext i; cases i using Fin.inductionOn <;> aesop ⟩
```

There are also reindexed versions for the Fin(2^n) indexing used later:

```lean
theorem huang_matrix_fin_isSymm (n : ℕ) : (huang_matrix_fin n).IsSymm := by
  exact funext fun i => funext fun j => huang_matrix_isSymm n |>.apply _ _

theorem huang_matrix_fin_sq (n : ℕ) : (huang_matrix_fin n) ^ 2 = (n : ℝ) • (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℝ) := by
  ext i j;
  simp +decide [ huang_matrix_fin, sq ];
  convert congr_fun ( congr_fun ( huang_matrix_sq n ) ( ( boolFunEquivFin n ).symm i ) ) ( ( boolFunEquivFin n ).symm j ) using 1 ; norm_num [ Matrix.mul_apply ];

theorem huang_matrix_fin_trace (n : ℕ) : Matrix.trace (huang_matrix_fin n) = 0 := by
  -- The trace of the reindexed matrix is the same as the original matrix, which is 0 by huang_matrix_trace. Hence, we can conclude.
  have h_trace_reindex : Matrix.trace (Matrix.reindex (boolFunEquivFin n) (boolFunEquivFin n) (huang_matrix n)) = Matrix.trace (huang_matrix n) := by
    exact trace_reindex_eq_trace (boolFunEquivFin n) (huang_matrix n)
  exact h_trace_reindex.trans ( huang_matrix_trace n )
```

Even if you do not read Lean, the intent is simple: each theorem formalizes one of the three invariants listed above.

## Why these three facts determine the spectrum
A quick sketch that does not require heavy linear algebra:

- Because A_n is symmetric, it has real eigenvalues and can be diagonalized.
- If v is an eigenvector with eigenvalue lambda, then A_n^2 v = lambda^2 v.
- But A_n^2 = n I, so A_n^2 v = n v, which forces lambda^2 = n.
- Therefore every eigenvalue is either +sqrt(n) or -sqrt(n).
- The trace is the sum of all eigenvalues. Trace 0 means the positives and negatives cancel, so the counts of +sqrt(n) and -sqrt(n) are equal.

That is exactly the conclusion stated in HUANG_SPEC.

## Dependencies and what depends on it (from breakdown.md)
- Depends on: **HUANG_DEF** (the recursive block definition of A_n). The proof of symmetry and the A_n^2 identity is by induction on that block structure.
- Used by: **HUANG_SPEC** (to conclude the explicit spectrum) and **HUANG_REIDX** (to carry these properties to the Fin(2^n) indexing used for submatrices and induced graphs).
- Downstream impact: through HUANG_SPEC and HUANG_REIDX, these properties feed the interlacing lower bound and ultimately the sensitivity lower bound.

## Connection to neighboring concepts in the proof
Right before HUANG_PROP, the matrix A_n is defined (HUANG_DEF). Right after HUANG_PROP, the proof extracts the clean eigenvalue list (HUANG_SPEC). Then HUANG_REIDX moves the matrix to a different indexing so it can be compared directly with induced subgraphs of the hypercube.

So HUANG_PROP is the "engine tuning" step: it takes the raw matrix definition and turns it into the exact algebraic facts that make the spectral part of the proof go.

## Small example intuition (n = 1)
For n = 1,

```
A_1 = [ [0, 1],
        [1, 0] ]
```

- Symmetry is obvious.
- A_1^2 = I, which is 1 * I, so n = 1.
- Trace is 0 (diagonal entries are both 0).

Already at n = 1 you can see the pattern: the matrix is symmetric, squaring gives a scaled identity, and there is no diagonal bias. The higher-n matrices are engineered to preserve exactly those properties.

## Prerequisites (lightweight)
You only need basic matrix ideas: matrix multiplication, the identity matrix, the trace, and the notion that eigenvalues of symmetric matrices are real. If you want the full story, read HUANG_DEF first for the definition of A_n.
