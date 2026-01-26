# HUANG_DEF: Huang matrix A_n (recursive block form)

## Intuition and motivation
The proof needs a matrix tied to the n-dimensional hypercube graph whose eigenvalues are easy to control. The ordinary adjacency matrix of the hypercube is the obvious choice, but its spectrum is not as clean to handle in the proof. Huang's idea is to define a closely related matrix, A_n, that keeps the same "where the edges are" pattern but flips signs in a clever way. That small change makes A_n satisfy A_n^2 = n I, which forces its eigenvalues to be exactly +/- sqrt(n). This neat spectrum is the engine for the later eigenvalue and interlacing arguments.

## Plain-language definition
Think of the hypercube Q_n as all n-bit strings. Two strings are neighbors if they differ in exactly one bit. A matrix with rows and columns indexed by these strings can encode the graph: entry (u, v) is nonzero exactly when u and v are neighbors.

The Huang matrix A_n is built so that:
- It has the same zero/nonzero pattern as the hypercube adjacency matrix.
- The nonzero entries are +/- 1 instead of all +1.
- The signs are chosen recursively so that the whole matrix "squares to n".

The recursion mirrors how you build an (n+1)-cube from two n-cubes: one copy for strings starting with 0 and one for strings starting with 1, with matching edges between them.

## Recursive block formula (from the notes)
In `sensitivity-polynomial.tex`, the definition is:

```tex
A_1 = B_1 :=
  \begin{pmatrix}
  0 & 1 \\
  1 & 0
  \end{pmatrix}

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

What this means in words:
- The two diagonal blocks correspond to edges within each copy of the n-cube.
- The off-diagonal identity matrices connect each vertex to its twin in the other copy (flip the first bit).
- The only difference between A_{n+1} and the usual adjacency matrix B_{n+1} is the minus sign in the bottom-right block.

That minus sign is the "trick" that makes A_n have a perfectly balanced spectrum later.

## How Lean encodes the same idea
The Lean formalization builds the same block matrix but has to manage the indexing carefully. It first establishes several equivalences to convert between different representations of hypercube vertices.

### Supporting equivalences

First, an equivalence between `Bool × α` and the sum type `α ⊕ α`:

```lean
/-
Equivalence between Bool x alpha and alpha + alpha.
-/
def boolProdEquivSum_custom {α : Type*} : Bool × α ≃ α ⊕ α where
  toFun := fun p => if p.1 then Sum.inr p.2 else Sum.inl p.2
  invFun := fun s => match s with
    | Sum.inl a => (false, a)
    | Sum.inr a => (true, a)
  left_inv := by
    rintro ⟨ _ | _, _ ⟩ <;> simp +decide
  right_inv := by
    rintro (a | a) <;> rfl
```

Next, an equivalence between functions from `Fin (n+1)` and pairs of a value with a function from `Fin n`:

```lean
/-
Equivalence between functions from Fin (n+1) to alpha and pairs of (alpha, function from Fin n to alpha).
-/
def finSuccEquiv_custom (n : ℕ) (α : Type*) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun f := (f 0, f ∘ Fin.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    ext i
    refine Fin.cases ?_ ?_ i <;> simp
  right_inv p := by
    ext <;> simp
```

Composing these gives the key equivalence that splits an (n+1)-bit string into two copies of n-bit strings (based on the first bit):

```lean
/-
Equivalence between functions from Fin (n+1) to Bool and the sum of two copies of functions from Fin n to Bool.
-/
def finSuccEquiv_huang_custom (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Fin n → Bool) ⊕ (Fin n → Bool) :=
  Equiv.trans
    (finSuccEquiv_custom n Bool)
    (boolProdEquivSum_custom)
```

### The Huang matrix definition

With the equivalences in place, the Huang matrix is defined recursively using `Matrix.fromBlocks` and `Matrix.reindex`:

```lean
/-
The Huang matrix A_n is defined recursively. A_0 is 0. A_{n+1} is a block matrix with A_n on the diagonal, I on the off-diagonal, and -A_n on the other diagonal, reindexed to match the boolean hypercube indices.
-/
def huang_matrix (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  match n with
  | 0 => 0
  | n + 1 => Matrix.reindex (finSuccEquiv_huang_custom n).symm (finSuccEquiv_huang_custom n).symm
      (Matrix.fromBlocks (huang_matrix n) (1 : Matrix _ _ ℝ) (1 : Matrix _ _ ℝ) (-huang_matrix n))
```

The math content is the same as the TeX definition:
- The base case `n = 0` gives the zero matrix (a 1x1 matrix indexed by the empty function type).
- The recursive case uses `Matrix.fromBlocks` to construct the 2x2 block structure with `huang_matrix n` in the top-left, identity matrices on the off-diagonals, and `-huang_matrix n` in the bottom-right.
- The `Matrix.reindex` with `finSuccEquiv_huang_custom n` is bookkeeping to ensure the block matrix (naturally indexed by the sum type) gets re-indexed by actual (n+1)-bit Boolean strings.

## Dependencies and what depends on it
From `history/breakdown.md`, the HUANG_DEF atom:
- Depends on **BC4** (dimension-splitting equivalences). This is exactly the "split an (n+1)-bit string into its first bit plus the remaining n bits" step that makes the block recursion precise.
- Feeds into **HUANG_PROP** (symmetry, A_n^2 = n I, trace = 0), **ABS_ADJ** (|A_n| matches the hypercube adjacency), and **HUANG_REIDX** (move to Fin(2^n) indexing). It also feeds the LaTeX exposition (**INF_TEX**) that narrates the same definition.

So HUANG_DEF is the seed: once you have the matrix defined recursively, everything about its spectrum and its relationship to the hypercube graph can be proved.

## Connection to neighboring proof steps
Just before this point, the proof has isolated a large subset of hypercube vertices (a big level set of a transformed function). The next steps need a matrix with:
1) known eigenvalues, and
2) entries that reflect adjacency in the hypercube.

HUANG_DEF provides that matrix. After it is defined:
- **HUANG_PROP** and **HUANG_SPEC** extract the exact eigenvalues (+/- sqrt(n)).
- **ABS_ADJ** shows that ignoring signs gives the hypercube adjacency matrix.
- Later, principal submatrices of A_n are compared to induced subgraphs of the level set, bridging eigenvalues to graph degrees, and finally to sensitivity.

## Small example to build intuition
- For n = 1, A_1 is just the 2x2 matrix with off-diagonal 1s. This is also the adjacency matrix of the 1-cube.
- For n = 2, A_2 is built from A_1 in four blocks. The top-left block is A_1, the bottom-right block is -A_1, and the off-diagonal blocks are identity matrices. The pattern of nonzeros matches the 2-cube, but half of those edges now carry a minus sign.

That sign pattern is exactly what makes the algebra later work out cleanly.
