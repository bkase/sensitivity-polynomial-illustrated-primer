# ROWSUM_BOUND - Eigenvalue <= max absolute row sum

## Intuition and motivation
At this point in the proof, we have a matrix that encodes a graph (an adjacency matrix or something entrywise bounded by one). We want to turn a statement about matrix eigenvalues into a statement about graph degrees. ROWSUM_BOUND is the bridge: it says no eigenvalue can be larger (in absolute value) than the biggest total weight sitting in any single row. For a graph adjacency matrix, a row sum is just the degree of that vertex. So this lemma is the step that converts spectral information into a simple combinatorial quantity.

An analogy: imagine each row is a person who can distribute at most K units of "influence" to others (the absolute row sum). An eigenvector is a pattern of activity that is scaled uniformly by the matrix. ROWSUM_BOUND says the system cannot amplify any pattern by more than the maximum influence budget of a single row.

## Plain-language statement
For any real square matrix A and any eigenvalue mu of A,

```
|mu| <= max_i sum_j |A[i,j]|
```

The right-hand side is the maximum absolute row sum (also called the matrix infinity norm). So every eigenvalue is bounded in magnitude by the largest row total.

## Why it is true (core idea)
Pick a nonzero eigenvector v with A v = mu v. Look at the entry v_i with the largest absolute value. Now focus on row i:

```
mu * v_i = (A v)_i = sum_j A[i,j] * v_j
```

Take absolute values and use the triangle inequality:

```
|mu| * |v_i|
  = |sum_j A[i,j] * v_j|
 <= sum_j |A[i,j]| * |v_j|
 <= (sum_j |A[i,j]|) * |v_i|
```

The last step uses that |v_i| is the maximum, so |v_j| <= |v_i| for all j. Since v is nonzero, |v_i| > 0, so you can cancel it and get:

```
|mu| <= sum_j |A[i,j]|
```

Finally, take the maximum over rows. That is the entire argument: pick the biggest coordinate of the eigenvector and compare one row of A against it.

## How it appears in the LaTeX notes
The LaTeX proof uses this fact implicitly when it says the top eigenvalue is bounded by the row weight:

```tex
Let H_1 be the adjacency matrix of (Q_n)_S. It is obtained by deleting some rows
and the corresponding columns of the matrix for B_n. Then \lambda_1(H_1) \le d_S(g)
 because the weight of a row is at most d_S(g).
```

"Weight of a row" here means the sum of absolute values in that row. For a 0/1 adjacency matrix, that sum is exactly the degree.

## How it is formalized in Lean
The lemma is called `eigenvalue_le_max_row_sum` and states exactly the bound above:

```lean
theorem eigenvalue_le_max_row_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
  (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
  ∃ i : Fin n, |μ| ≤ Finset.sum Finset.univ (fun j => |A i j|) := by
    -- Let v be a nonzero eigenvector. Let i be the index maximizing |v_i|.
    obtain ⟨v, hv⟩ : ∃ v : Fin n → ℝ, v ≠ 0 ∧ A.mulVec v = μ • v := by
      obtain ⟨ v, hv ⟩ := hμ.exists_hasEigenvector;
      cases hv ; aesop
    obtain ⟨i, hi⟩ : ∃ i : Fin n, ∀ j : Fin n, |v j| ≤ |v i| := by
      have := Finset.exists_max_image Finset.univ ( fun i => |v i| ) ⟨ ⟨ 0, Nat.pos_of_ne_zero ( by aesop_cat ) ⟩, Finset.mem_univ _ ⟩ ; aesop;
    -- Then |μ v_i| = |(Av)_i| = |sum_j A_ij v_j| ≤ sum_j |A_ij| |v_j| ≤ sum_j |A_ij| |v_i| = |v_i| sum_j |A_ij|.
    have h_bound : |μ * v i| ≤ |v i| * ∑ j, |A i j| := by
      have h_bound : |μ * v i| = |∑ j, A i j * v j| := by
        have := congr_fun hv.2 i; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
      rw [ h_bound, Finset.mul_sum _ _ _ ];
      exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun j _ => by rw [ abs_mul, mul_comm ] ; exact mul_le_mul_of_nonneg_right ( hi j ) ( abs_nonneg _ ) );
    exact ⟨ i, by
      rw [ abs_mul ] at h_bound
      refine le_of_not_gt ?_
      intro hi'
      have hvipos : 0 < |v i| := by
        apply abs_pos.mpr
        intro hi''
        exact hv.1 <| funext fun j => by simpa [ hi'' ] using hi j
      have hgtmul : |μ| * |v i| > |v i| * ∑ j, |A i j| := by
        nlinarith [hi', hvipos]
      exact (not_le_of_gt hgtmul) h_bound ⟩
```

The proof follows the exact reasoning sketched above: choose an eigenvector `v`, pick the index `i` where `|v i|` is largest, and apply the triangle inequality.

## Dependencies and downstream links (from breakdown.md)
**What ROWSUM_BOUND represents:**
- A general linear-algebra inequality: any eigenvalue is bounded by a maximum absolute row sum.

**Depends on:**
- No prior proof atoms in the breakdown graph. It is a stand-alone linear algebra fact (it does rely on the basic notion of eigenvalue/eigenvector and the triangle inequality).

**What depends on ROWSUM_BOUND:**
- **SPEC_UPPER**, which combines this lemma with the adjacency-entry bound to conclude
  ``lambda_max(A_n_fin[S]) <= maxDegree(induced graph)``.
- Downstream, that feeds into the full-case sensitivity bound, but the direct consumer is SPEC_UPPER.

## How it connects to neighboring concepts
ROWSUM_BOUND is paired with **SUBMAT_BOUND** and **SPEC_UPPER**:
- **SUBMAT_BOUND** says the submatrix entries are bounded by a 0/1 adjacency indicator.
- **ROWSUM_BOUND** converts "entrywise bound" into "eigenvalue bound" by using row sums.
- **SPEC_UPPER** combines those two to say the spectral radius of the submatrix is at most the maximum degree of the induced graph.

So ROWSUM_BOUND is the local spectral-to-combinatorial translator in the proof chain.

## Prerequisite pointers
If you want to dive deeper:
- Eigenvalues and eigenvectors (basic linear algebra definitions).
- Triangle inequality for sums and absolute values.
- Adjacency matrices and vertex degree in graphs (why a row sum equals degree in 0/1 matrices).

If you only remember one thing: ROWSUM_BOUND says "no eigenvalue can exceed the biggest total weight of any row," which is exactly what lets the proof turn matrix bounds into graph-degree bounds.
