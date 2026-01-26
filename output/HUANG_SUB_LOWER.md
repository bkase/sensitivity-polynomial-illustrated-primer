# HUANG_SUB_LOWER

## What this atom is (from breakdown.md)
**HUANG_SUB_LOWER** is the step that says:

> If you take the Huang matrix for dimension `n`, and you keep only a principal submatrix indexed by a set `S` that is **larger than half the vertices** (so `|S| > 2^(n-1)`), then the **largest eigenvalue** of that submatrix is at least `sqrt(n)`.

In the breakdown graph, it is described as: **“Apply interlacing + Huang spectrum; |S|>2^{n-1} ⇒ λ_max(A_n_fin[S]) ≥ sqrt(n)”**.

### Dependencies and dependents (as shown in the DAG)
- **Depends on:**
  - **INTERLACE** (principal-submatrix interlacing lemma)
  - **HUANG_SPEC** (explicit eigenvalues of the Huang matrix)
  - It is *applied using* **LEVELSETS** (gives a set `S` bigger than half), although that set-size fact is not part of the algebraic statement itself.
- **Used by:**
  - **FULLCASE** (the core theorem for full degree), where it is paired with a spectral upper bound to force large sensitivity.

## Intuition and motivation (why we need this)
The proof wants to turn “a big subset of the hypercube” into “a big sensitivity.” The way it does that is by **spectral comparison**:

- A **lower bound** on the largest eigenvalue of a matrix built from `S` tells you that something in `S` is “highly connected.”
- An **upper bound** on that eigenvalue, computed from graph degrees, tells you how connected it *can* be.

To make the lower bound strong, we use a special matrix (the **Huang matrix**) whose eigenvalues are known exactly. If the submatrix is **large enough**, interlacing forces it to inherit a big eigenvalue (at least `sqrt(n)`). That is exactly what HUANG_SUB_LOWER provides.

If this step failed, we could have a large subset with no spectral “signal,” and the later sensitivity bound would collapse.

## Plain-language picture
Think of the Huang matrix as a **tuning fork** with only two possible “notes”: a low note `-sqrt(n)` and a high note `+sqrt(n)`, each appearing exactly half the time.

Now pick a large subset `S` of the vertices (more than half of them) and keep only the rows/columns inside `S`. Interlacing says: **you cannot cut out a huge part of a tuning fork and lose all of the high notes**. If the submatrix is big enough, at least one of its eigenvalues must still be at the high note `+sqrt(n)`.

That high note is the quantitative lower bound we need.

## The key math idea (interlacing + spectrum)
Let:
- `A` be the Huang matrix (reindexed as `A_n_fin`), size `2^n x 2^n`.
- `A[S]` be the principal submatrix on a vertex set `S`.
- `m = |S|`.

Two facts:
1. **Spectrum of the full matrix** (HUANG_SPEC):
   - The eigenvalues of `A` are exactly
     `(-sqrt(n), ..., -sqrt(n), +sqrt(n), ..., +sqrt(n))`,
     with **half** negative and **half** positive.
2. **Interlacing** (INTERLACE):
   - The largest eigenvalue of `A[S]` is at least the `m`-th smallest eigenvalue of `A`.

If `m > 2^(n-1)`, then the `m`-th eigenvalue of `A` lands in the **positive half**, so it is `+sqrt(n)`. Therefore:

```
lambda_max(A[S]) >= sqrt(n)
```

That is the HUANG_SUB_LOWER statement.

## Connection to neighboring concepts in the proof
Here is how this atom plugs into the proof flow:

1. **LEVELSETS** produces a set `S` of vertices where a transformed function `g` is +1 (or -1), and shows `|S| > 2^(n-1)`.
2. **HUANG_SUB_LOWER** applies interlacing + Huang’s spectrum to that large `S`, giving:
   - `lambda_max(A_n_fin[S]) >= sqrt(n)`.
3. **SPEC_UPPER** bounds the same eigenvalue from above using graph degrees:
   - `lambda_max(A_n_fin[S]) <= maxDegree(induced_graph_on_S)`.
4. **DEG_SENS_LEVEL** identifies that graph degree with sensitivity counts.
5. Combine: `sqrt(n) <= maxDegree(...) <= sensitivity(f)`.

So HUANG_SUB_LOWER is the “spectral lower bound” half of the squeeze.

## Lean snippet (formal statement)
From `sensitivity.lean`:

```lean
lemma huang_submatrix_max_eigenvalue_ge_sqrt_n {n : ℕ} (hn : n ≠ 0)
  (S : Finset (Fin (2^n))) (hS : S.card > 2^(n-1)) :
  let subA := principal_submatrix_fin (huang_matrix_fin n) S
  let h_subA := principal_submatrix_fin_isSymm (huang_matrix_fin n) (huang_matrix_fin_isSymm n) S
  let evs_sub := sorted_eigenvalues subA h_subA
  evs_sub.getLast (List.ne_nil_of_length_pos (by
  rw [ sorted_eigenvalues_length ];
  exact Fintype.card_pos_iff.mpr ⟨ Classical.choose ( Finset.card_pos.mp ( pos_of_gt hS ) ), Classical.choose_spec ( Finset.card_pos.mp ( pos_of_gt hS ) ) ⟩)) ≥ Real.sqrt n := by
    have h_max_eigenvalue_ge_sqrt : let m := S.card
      let subA := principal_submatrix_fin (huang_matrix_fin n) S
      let h_subA := principal_submatrix_fin_isSymm (huang_matrix_fin n) (huang_matrix_fin_isSymm n) S
      let evs_sub := sorted_eigenvalues subA h_subA
      evs_sub.getLast (List.ne_nil_of_length_pos (by
      have hSpos : 0 < S.card := lt_of_le_of_lt (Nat.zero_le _) hS
      have hlen : evs_sub.length = S.card := by
        simp [evs_sub, sorted_eigenvalues_length, Fintype.card_coe]
      rw [hlen]
      exact hSpos)) ≥ (sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)).get ⟨m - 1, by
        rw [ sorted_eigenvalues_length ];
        exact lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt hS ) ) ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )⟩ := by
        apply eigenvalue_interlacing_max;
        exact Finset.card_pos.mp ( pos_of_gt hS )
    have h_eigenvalues_eq_list : let evs := sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)
      evs = List.replicate (2^(n-1)) (-Real.sqrt n) ++ List.replicate (2^(n-1)) (Real.sqrt n) := by
        exact huang_eigenvalues_eq_list n hn
    simp_all +decide [ List.getElem_append ];
    exact le_trans ( by rw [ if_neg ( by omega ) ] ) h_max_eigenvalue_ge_sqrt
```

How to read it:
- `principal_submatrix_fin` is the “keep only rows/cols in S” operation.
- `sorted_eigenvalues` lists eigenvalues in nondecreasing order.
- `getLast` is the maximum eigenvalue.
- The proof uses `eigenvalue_interlacing_max` (interlacing) plus `huang_eigenvalues_eq_list` (explicit spectrum) to conclude the bound.

## LaTeX snippet (informal math version)
From the lecture notes:

```tex
If we negate entries of H_1 appropriately we obtain some H_2, a submatrix of A_n.
By lemma \ref{cauchy}, \lambda_1(H_2) > \lambda_{2^{n-1}}(A_n) = \sqrt n.
```

The `\lambda_{2^{n-1}}(A_n) = sqrt(n)` step is exactly the “Huang spectrum + half-size” logic, and `H_2` is the relevant principal submatrix.

## Summary in one sentence
HUANG_SUB_LOWER says: **a principal submatrix of the Huang matrix that keeps more than half the vertices must still have a top eigenvalue at least `sqrt(n)`**, because interlacing forces it to inherit a positive eigenvalue from the full matrix’s explicit `±sqrt(n)` spectrum.
