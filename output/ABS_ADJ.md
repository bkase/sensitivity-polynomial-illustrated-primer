# ABS_ADJ: |A_n| matches hypercube adjacency

## Intuition and motivation
The proof needs to connect two different viewpoints:
1) A matrix viewpoint, where eigenvalues are easy to analyze, and
2) A graph viewpoint, where "degree" corresponds to sensitivity.

The Huang matrix A_n is designed to have clean eigenvalues, but it uses +1 and -1 signs on edges. ABS_ADJ is the statement that if you ignore those signs (take absolute values), you recover the ordinary adjacency matrix of the hypercube. This is the exact bridge that says: "A_n is a signed version of the hypercube adjacency matrix."

Without this bridge, later steps could not compare matrix entries to graph edges, so the eigenvalue bounds would not translate into degree bounds.

## Plain-language statement
Think of the n-dimensional hypercube Q_n as all n-bit strings. Two vertices are neighbors if they differ in exactly one bit.

The Huang matrix A_n is indexed by these vertices. Its entries are:
- +1 or -1 when two vertices are neighbors, and
- 0 when they are not neighbors.

ABS_ADJ says:

```
|A_n(i,j)| = 1 if i and j are neighbors
|A_n(i,j)| = 0 otherwise
```

So A_n has the same zero/nonzero pattern as the hypercube adjacency matrix; it just assigns signs to the edges.

## Connection to the LaTeX notes
In `sensitivity-polynomial.tex`, the matrix recursion is:

```tex
A_{n+1} :=
  \begin{pmatrix}
  A_n & I_{2^n} \\
  I_{2^n} & -A_n
  \end{pmatrix}

B_{n+1} :=
  \begin{pmatrix}
  B_n & I_{2^n} \\
  I_{2^n} & B_n
  \end{pmatrix}
```

The notes then point out that `B_n` is the adjacency matrix of Q_n, and `A_n` is "the same, but with some entries flipped." Taking absolute values removes those flips, so |A_n| matches B_n exactly. That is the ABS_ADJ concept in words.

## Lean statement (core idea)
The Lean formalization expresses adjacency by "Hamming distance = 1":

```lean
def hypercube_graph (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun x y =>
    (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1)
```

The ABS_ADJ lemma then states:

```lean
theorem abs_huang_eq_adjacency (n : ℕ) (i j : Fin n → Bool) :
  |huang_matrix n i j| = if (Finset.filter (fun k => i k ≠ j k) Finset.univ).card = 1 then 1 else 0 := by
    rcases n with ( _ | n );
    · aesop;
    · -- By induction on $n$, we can show that the absolute value of the entries of the Huang matrix is the adjacency matrix of the hypercube.
      have h_ind : ∀ n : ℕ, ∀ i j : Fin (n + 1) → Bool, |(huang_matrix (n + 1)) i j| = if (Finset.card (Finset.filter (fun k => i k ≠ j k) Finset.univ)) = 1 then 1 else 0 := by
        -- We proceed by induction on $n$.
        intro n
        induction' n with n ih;
        · simp +decide [ huang_matrix ];
          intro i j; fin_cases i <;> fin_cases j <;> simp +decide [ finSuccEquiv_huang_custom ] ;
          · rfl;
          · simp +decide [ boolProdEquivSum_custom, finSuccEquiv_custom ];
            simp +decide [ Matrix.one_apply ];
          · simp +decide [ boolProdEquivSum_custom, finSuccEquiv_custom ];
            simp +decide [ Matrix.one_apply ];
          · rfl;
        · intro i j;
          -- By definition of `huang_matrix`, we can split into cases based on whether `i` and `j` are in the same block or different blocks.
          have h_split : ∀ i j : Fin (n + 2) → Bool, |(huang_matrix (n + 2)) i j| = if (i 0 = j 0) then |(huang_matrix (n + 1)) (fun k => i (Fin.succ k)) (fun k => j (Fin.succ k))| else if (Finset.card (Finset.filter (fun k => i (Fin.succ k) ≠ j (Fin.succ k)) Finset.univ)) = 0 then 1 else 0 := by
            intros i j;
            have h_split : ∀ i j : Fin (n + 2) → Bool, |(huang_matrix (n + 2)) i j| = if (i 0 = j 0) then |(huang_matrix (n + 1)) (fun k => i (Fin.succ k)) (fun k => j (Fin.succ k))| else if (Finset.card (Finset.filter (fun k => i (Fin.succ k) ≠ j (Fin.succ k)) Finset.univ)) = 0 then 1 else 0 := by
              intro i j
              have h_def : huang_matrix (n + 2) = Matrix.reindex (finSuccEquiv_huang_custom (n + 1)).symm (finSuccEquiv_huang_custom (n + 1)).symm (Matrix.fromBlocks (huang_matrix (n + 1)) (1 : Matrix _ _ ℝ) (1 : Matrix _ _ ℝ) (-huang_matrix (n + 1))) := by
                exact rfl
              simp +decide [ h_def, Matrix.fromBlocks ];
              unfold finSuccEquiv_huang_custom;
              unfold finSuccEquiv_custom; simp +decide ;
              unfold boolProdEquivSum_custom; simp +decide ;
              split_ifs <;> simp +decide [ *, Matrix.one_apply ];
              all_goals simp_all +decide [ funext_iff ];
            exact h_split i j;
          rw [ show ( Finset.univ.filter fun k => i k ≠ j k ) = if i 0 = j 0 then Finset.image ( Fin.succ ) ( Finset.univ.filter fun k => i ( Fin.succ k ) ≠ j ( Fin.succ k ) ) else Finset.image ( Fin.succ ) ( Finset.univ.filter fun k => i ( Fin.succ k ) ≠ j ( Fin.succ k ) ) ∪ { 0 } from ?_ ];
          · split_ifs <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
          · ext ( _ | k ) <;> simp +decide;
            · split_ifs <;> simp +decide [ * ];
            · split_ifs <;> simp_all +decide [ Finset.mem_image, Finset.mem_insert ];
              · exact ⟨ fun h => ⟨ ⟨ k, by linarith ⟩, h, rfl ⟩, by rintro ⟨ a, ha, ha' ⟩ ; cases a ; aesop ⟩;
              · exact ⟨ fun h => ⟨ ⟨ k, by linarith ⟩, h, rfl ⟩, by rintro ⟨ a, h, ha ⟩ ; cases a ; aesop ⟩;
      exact h_ind n i j
```

Read it as: take any two vertices `i` and `j`. If they differ in exactly one bit, the Huang matrix entry has absolute value 1; otherwise it is 0. That is exactly the adjacency indicator of Q_n.

## Analogy
Imagine a road map where every road has a sign: either "+" or "-". The signs matter for algebra (eigenvalues), but not for whether two cities are connected by a road. ABS_ADJ says that A_n is this signed road map: erase the signs (absolute value), and you get the usual road map of the hypercube.

## Dependencies and what depends on it (from breakdown.md)
- **Depends on:** **HUANG_DEF**. You need the recursive definition of A_n to even talk about its entries and prove they align with hypercube adjacency.
- **Directly used by:** **HUANG_REIDX**. After establishing the adjacency pattern on `Fin n -> Bool`, the proof transports it to the `Fin (2^n)` indexing used for later matrix and graph comparisons.

Downstream, via HUANG_REIDX, this fact feeds into:
- **SUBMAT_BOUND** (entrywise comparison between Huang submatrices and induced graph adjacency),
- **SPEC_UPPER** (spectral radius bounded by max degree),
and ultimately the sensitivity lower bound.

## How it connects to neighboring steps
ABS_ADJ sits between:
- **HUANG_DEF**: defines A_n, which has the right signs and block structure.
- **HUANG_REIDX**: reindexes A_n so it can be compared directly with induced subgraphs on subsets of vertices.

In other words, once you know that |A_n| encodes hypercube adjacency, you can safely carry that fact through the reindexing step and then use it to compare matrix entries with graph edges.

## Tiny example (n = 2)
The 2-cube has vertices 00, 01, 10, 11. Each vertex is adjacent to the two vertices that differ in one bit. The adjacency matrix has 1s exactly at those pairs.

The Huang matrix A_2 has the same pattern of nonzero entries, but some of those 1s are flipped to -1. ABS_ADJ says that if you ignore the signs, the pattern is identical to the adjacency matrix of the 2-cube.

## Prerequisites (informal)
To follow ABS_ADJ comfortably, you only need:
- The definition of the hypercube graph Q_n (neighbors differ in exactly one bit).
- The recursive definition of the Huang matrix A_n (HUANG_DEF).

No Lean knowledge is required to understand the mathematical content, but the Lean lemma above shows the exact formal statement used in the proof.
