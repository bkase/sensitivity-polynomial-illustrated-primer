# BC4: Dimension-splitting equivalences (why we can build A_{n+1} from A_n)

## What BC4 is and why it exists

**BC4 is the "split the (n+1)-dimensional cube into two n-dimensional cubes" idea.**
It packages that split as **explicit bijections** (equivalences) between different ways of indexing cube vertices. This is needed for the *recursive* definition of the Huang matrix \(A_n\): to define \(A_{n+1}\) as a block matrix, we must be able to view the \((n+1)\)-cube as **two copies of the n-cube** (first bit 0 vs 1) and reindex the rows/columns accordingly.

In short:
- BC4 gives the **formal map** between an \((n+1)\)-bit string and `(first bit, remaining n bits)`.
- It then converts that pair into **either-left or either-right**, i.e., a **disjoint union** of two copies of the n-cube.
- This lets us arrange indices so that the Huang matrix naturally appears as a **2x2 block matrix** with \(A_n\), \(-A_n\), and identities in the right places.

## Dependencies and dependents (from breakdown.md)

- **Depends on:** nothing upstream in the dependency graph. (Conceptually, it relies only on the basic representation of cube vertices as functions `Fin n -> Bool` from BC0.)
- **Used by:** **HUANG_DEF** (the recursive definition of the Huang matrix). Everything that uses the Huang matrix (its properties, spectrum, adjacency comparison, etc.) then depends on BC4 *indirectly*.

## Intuition: two floors of the same building

Imagine the \((n+1)\)-cube as a building with two floors:
- Floor 0 = all vertices with first bit = 0.
- Floor 1 = all vertices with first bit = 1.

Each floor is an **n-cube** (same layout, same adjacency within the floor). The only edges that connect the floors are the ones that flip the first bit, which line up *point-to-point* across the two floors.

BC4 is the precise bookkeeping that lets us treat the whole building as:

```
(two copies of the n-cube) + the "elevator" edges between them
```

That bookkeeping is exactly what a block matrix needs.

## Plain-language statement of the equivalences

A vertex of the \((n+1)\)-cube is an \((n+1)\)-bit string.
There are two equivalent ways to describe such a vertex:

1) **Head + tail**: the first bit, plus the remaining n-bit string.
2) **Left or right copy**: choose the left copy if the first bit is 0, or the right copy if the first bit is 1.

So we have a chain of bijections:

```
(n+1)-bit string
  <-> (first bit, n-bit string)
  <-> (left copy of n-bit string) + (right copy of n-bit string)
```

The last step is the disjoint union (sum type) of two copies of the n-cube.

## The Lean code (BC4 in the formalization)

These are the exact equivalences used in the Lean file:

```lean
def boolProdEquivSum_custom {α : Type*} : Bool × α ≃ α ⊕ α where
  toFun := fun p => if p.1 then Sum.inr p.2 else Sum.inl p.2
  invFun := fun s => match s with
    | Sum.inl a => (false, a)
    | Sum.inr a => (true, a)
  left_inv := by
    rintro ⟨ _ | _, _ ⟩ <;> simp +decide
  right_inv := by
    rintro (a | a) <;> rfl

def finSuccEquiv_custom (n : ℕ) (α : Type*) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun f := (f 0, f ∘ Fin.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    ext i
    refine Fin.cases ?_ ?_ i <;> simp
  right_inv p := by
    ext <;> simp

def finSuccEquiv_huang_custom (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Fin n → Bool) ⊕ (Fin n → Bool) :=
  Equiv.trans
    (finSuccEquiv_custom n Bool)
    (boolProdEquivSum_custom)
```

### What this means (translated)
- `Fin (n+1) -> Bool` is a fancy way to say "an (n+1)-bit string".
- `Fin n -> Bool` is an n-bit string.
- `Sum.inl` and `Sum.inr` are the left and right copies of the n-cube.
- `finSuccEquiv_custom` says: **an (n+1)-bit string = (first bit, remaining bits)**.
- `boolProdEquivSum_custom` says: **a pair (bit, x) is either left-x or right-x**.
- Composing those gives the split of the cube into two copies.

## How this enables the recursive Huang matrix

Once the index set is split into two copies, the matrix can be written in block form. The LaTeX notes define it like this:

```tex
A_1 = B_1 := \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}

A_{n+1} := \begin{pmatrix}
  A_n & I \\
  I & -A_n
\end{pmatrix}

B_{n+1} := \begin{pmatrix}
  B_n & I \\
  I & B_n
\end{pmatrix}
```

Interpretation:
- The **top-left block** is adjacency *within* the first copy (first bit = 0).
- The **bottom-right block** is adjacency *within* the second copy (first bit = 1).
- The **off-diagonal identity blocks** represent the edges that flip the first bit (the vertical edges between floors).
- The **minus sign** in \(-A_n\) is what makes the Huang matrix different from the ordinary adjacency matrix.

In Lean, the split is used via `Matrix.reindex` and `Matrix.fromBlocks`:

```lean
def huang_matrix (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  match n with
  | 0 => 0
  | n + 1 => Matrix.reindex (finSuccEquiv_huang_custom n).symm (finSuccEquiv_huang_custom n).symm
      (Matrix.fromBlocks (huang_matrix n) (1 : Matrix _ _ ℝ) (1 : Matrix _ _ ℝ) (-huang_matrix n))
```

So BC4 is the **indexing trick** that makes this definition well-typed and meaningful.

## Connection to neighboring concepts in the proof

- **Before BC4:** BC0 and BC1 set up the Boolean cube and adjacency. BC4 does not use adjacency itself; it uses only the *representation* of cube vertices as `Fin n -> Bool`.
- **After BC4:** HUANG_DEF immediately uses this split to define \(A_{n+1}\). The spectral facts (HUANG_PROP, HUANG_SPEC) and the adjacency comparison (ABS_ADJ) all rely on this block form. Those pieces then power the interlacing lower bound and, ultimately, the sensitivity inequality.

## Why this matters in the big picture

The Sensitivity Conjecture proof needs a matrix whose eigenvalues are easy to control but whose absolute values still "look like" the hypercube adjacency matrix. The Huang matrix \(A_n\) is exactly that. **BC4 is the door that lets us build \(A_{n+1}\) from \(A_n\)** by treating the cube as two stacked copies. Without this clean split, the recursive construction (and the clean eigenvalue proof that follows) would be much harder to express.

## Quick mental model

- Think of all \((n+1)\)-bit strings.
- Group them by the first bit.
- You now have two identical n-cubes with a perfect matching between them.
- BC4 formalizes that grouping so the block matrix definition of \(A_{n+1}\) is precise.

That is the entire role of BC4: **dimension-splitting equivalences that power the recursive block structure of the Huang matrix.**
