# SPEC_UPPER - From adjacency bound to eigenvalue <= max degree

Intuition and motivation
In the proof, we build a special matrix (a submatrix of the Huang matrix) from a large subset of cube vertices. Interlacing gives a LOWER bound on its largest eigenvalue (at least sqrt(n)), but sensitivity is a graph degree quantity. SPEC_UPPER is the missing bridge: it turns an eigenvalue statement into a max-degree statement. Once we know "largest eigenvalue <= max degree," we can compare it directly to sensitivity.

Plain-language definition
SPEC_UPPER says: if you have a symmetric matrix A whose entries only live on the edges of a graph G (and are at most 1 in absolute value), then the largest eigenvalue of A is at most the maximum degree of G.

In the proof, A is the principal submatrix A_n_fin[S] of the Huang matrix on a vertex subset S, and G is the induced hypercube graph on S. So the statement becomes:

```
lambda_max(A_n_fin[S]) <= maxDegree(induced graph on S)
```

Why this should be true (row-sum intuition)
Think of A as a machine that takes a vector and mixes its entries. An eigenvalue is a direction that just gets scaled by some factor mu. If we pick the index i where the eigenvector is largest in magnitude, then the i-th coordinate of A*v can be at most the sum of absolute weights in row i. That gives the row-sum bound:

```
|mu| <= sum_j |A_ij|
```

Now use the adjacency bound: if A_ij is nonzero only when i is adjacent to j, and |A_ij| <= 1, then the row sum is at most the number of neighbors of i. So:

```
sum_j |A_ij| <= degree(i)
```

Taking the worst case over all rows, we get:

```
lambda_max(A) <= max_i degree(i) = maxDegree(G)
```

Analogy
Imagine a network where each node sends up to 1 unit of signal to each neighbor. The strongest "amplification" any direction can get is limited by the node with the most neighbors. That is exactly the max degree.

How it connects to neighboring concepts
- SUBMAT_BOUND: gives the entrywise adjacency bound for the Huang submatrix. This is the hypothesis needed to turn row-sums into degrees.
- ROWSUM_BOUND: the general linear-algebra fact that an eigenvalue is bounded by a max row sum.
- BC2 (induced graphs + maxDegree): supplies the graph degree notion.
- SPEC_UPPER then feeds into FULLCASE by combining the interlacing lower bound (lambda_max >= sqrt(n)), the SPEC_UPPER upper bound (lambda_max <= maxDegree), and the degree-to-sensitivity bridge to conclude sensitivity >= sqrt(n).

How it appears in the LaTeX notes
The lecture notes use the same idea in the main proof:
```tex
Let H_1 be the adjacency matrix of (Q_n)_S. ... Then
lambda_1(H_1) <= d_S(g) because the weight of a row is at most d_S(g).
```
Here, the "weight of a row" is the row-sum bound, and d_S(g) is the max degree in the induced subgraph.

How it is formalized in Lean
The core lemma is `spectral_radius_bound`, which packages both the row-sum bound and the adjacency bound:
```lean
theorem spectral_radius_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (G : SimpleGraph (Fin n))
  (h_adj : ∀ i j, |A i j| ≤ if G.Adj i j then 1 else 0) (hn : n ≠ 0) :
  let evs := sorted_eigenvalues A hA
  let lambda_max := evs.getLast (List.ne_nil_of_length_pos (by rw [sorted_eigenvalues_length A hA]; exact Nat.pos_of_ne_zero hn))
  lambda_max ≤ G.maxDegree := by
    -- Since the largest eigenvalue is bounded by the maximum degree of the graph (from Lemma~\ref{lem:eigenvalue_le_max_row_sum}), we have:
    have h_bound : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ ≤ G.maxDegree := by
      intro μ hμ
      obtain ⟨i, hi⟩ := eigenvalue_le_max_row_sum A μ hμ;
      -- Since $|A i j| \leq 1$ if $G.Adj i j$ and $0$ otherwise, we have $\sum j, |A i j| \leq \sum j in G.neighborFinset i, 1$.
      have h_sum_le_neighbor : ∑ j, |A i j| ≤ ∑ j ∈ G.neighborFinset i, 1 := by
        exact le_trans ( Finset.sum_le_sum fun _ _ => h_adj _ _ ) ( by simp +decide [ SimpleGraph.neighborFinset_def ] );
      exact le_trans ( le_abs_self μ ) ( hi.trans <| h_sum_le_neighbor.trans <| mod_cast by simpa using G.degree_le_maxDegree i );
    have h_sorted : ∀ μ ∈ sorted_eigenvalues A hA, μ ≤ G.maxDegree := by
      intros μ hμ
      obtain ⟨i, hi⟩ : ∃ i : Fin n, μ = Matrix.IsHermitian.eigenvalues ((isSymm_iff_isHermitian_real A).mp hA) i := by
        unfold sorted_eigenvalues at hμ; aesop;
      convert h_bound μ ?_;
      have := ( Matrix.IsHermitian.eigenvalues_eq hA );
      simp_all +decide [ Module.End.HasUnifEigenvalue ];
      simp_all +decide [ Submodule.eq_bot_iff ];
      exact ⟨ _, by simpa [ this ] using Matrix.IsHermitian.mulVec_eigenvectorBasis hA i, by simpa [ this ] using ( Matrix.IsHermitian.eigenvectorBasis hA ).orthonormal.ne_zero i ⟩;
    exact h_sorted _ <| List.getLast_mem _
```
In the full-degree proof, this is applied to the Huang submatrix:
```lean
have h_adj : ∀ i j,
  |subA i j| ≤ if (induced_hypercube_graph_fin_card S).Adj i j then 1 else 0 := by
  ... -- from huang_submatrix_bounded_by_induced_adjacency

have h_lambda_le_max :
  evs_sub.getLast h_ne ≤ (induced_hypercube_graph_fin_card S).maxDegree := by
  ... spectral_radius_bound ...
```

Connections in the proof graph
What SPEC_UPPER depends on (from breakdown.md):
- ROWSUM_BOUND (eigenvalue <= max absolute row sum)
- SUBMAT_BOUND (entries bounded by induced adjacency)
- BC2 (induced subgraph + maxDegree)

What depends on SPEC_UPPER:
- FULLCASE (the main degree = n case), and therefore the final theorem.

If you only remember one thing
SPEC_UPPER is the "eigenvalues to degrees" bridge: once a matrix is controlled by a graph's adjacency, its largest eigenvalue cannot exceed the graph's maximum degree. That is the step that lets spectral lower bounds translate into sensitivity bounds.
