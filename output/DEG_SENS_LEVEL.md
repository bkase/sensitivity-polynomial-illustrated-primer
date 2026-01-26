# DEG_SENS_LEVEL: sensitivity equals induced degree on a big level set

## Intuition and motivation

The Sensitivity Conjecture is about how often a Boolean function flips when you toggle one input bit. That is a local, point-by-point notion: for each input x, count how many single-bit neighbors y make f(x) != f(y). The proof, however, wants to use spectral (matrix) bounds on graphs, which are global. To connect those worlds, we need a bridge: a way to rephrase "how many flips" as "how many edges inside a graph." That bridge is exactly what the DEG_SENS_LEVEL atom provides.

Informally:

- Sensitivity counts edges where f changes.
- A graph degree counts edges staying inside a chosen subset of vertices.
- By re-labeling the function as g, we can make those two counts match.

So DEG_SENS_LEVEL is the step that lets a sensitivity bound become a graph degree bound, which is what the spectral machinery later consumes.

## What the atom says (plain language)

After we define g(x) by twisting f(x) with parity, we split the cube into two level sets: where g(x) = +1 and where g(x) = -1. The key neighbor rule says: along an edge, g stays the same exactly when f flips. So if you look inside one level set (say g = +1), the number of neighbors of x that stay inside that level set is exactly the number of neighbors where f flips. In other words, for any x in that level set,

"degree of x in the induced subgraph" = "sensitivity of f at x".

Taking the maximum over x, this gives:

- the maximum degree in the induced subgraph is at most the overall sensitivity of f.

This is the precise bridge the proof needs.

## Dependencies and what depends on it

**Depends on** (from breakdown.md):

- **SEN0**: definition of sensitivity (count neighbors where f changes).
- **BC2**: induced subgraph and graph degree/maxDegree.
- **LEVELSETS**: one of the level sets of g is large.
- **NEIGH_RULE**: for neighbors x ~ y, g(x) = g(y) iff f(x) != f(y).

**Used by**:

- **FULLCASE**: the main degree=n case. This step supplies the inequality "maxDegree <= sensitivity" for the large level set, so the spectral upper bound can be stated in terms of sensitivity.

## The core idea with an analogy

Think of the Boolean cube as a big grid of rooms, one per input x. Each room is connected to neighbors that differ in exactly one bit. The function f is a light that is either ON or OFF in each room. Sensitivity at x is: how many doorways from x lead to a room where the light switches.

Now define g by multiplying f's light by a checkerboard coloring of the cube (the parity character). This checkerboard flips sign across every doorway. Because of that, when you compare two adjacent rooms:

- if the checkerboard flips but f stays the same, g changes,
- if the checkerboard flips and f flips too, g stays the same.

So "g stays the same" along a doorway is equivalent to "f flips" along that doorway. That means: inside the region where g is constant (+1 or -1), the number of internal doorways from x is exactly the number of f-flipping neighbors of x. Those internal doorways are exactly the degree of x in the induced subgraph on that region.

## How the LaTeX notes phrase it

From `sensitivity-polynomial.tex`, the transformation and the consequence are summarized as:

```tex
let g(x) := f(x) \chi_{[n]}.
Let S := { x | g(x) = 1 }.
Then sensitivity becomes
s(f) = max(d_S(g), d_{Q_n \setminus S}(g)).
```

Here d_S(g) means the maximum degree in the induced subgraph on S. The statement is a compact way of saying: within either level set, graph degree counts exactly the sensitive neighbors.

## The Lean formalization (key snippets)

Lean defines g and the level sets like this:

```lean
def g_val {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℝ :=
  (if f x then -1 else 1) * chi Finset.univ x

def S_pos {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.filter (fun x => g_val f x = 1) Finset.univ

def S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.filter (fun x => g_val f x = -1) Finset.univ
```

The key bridge lemma for the positive level set is:

```lean
lemma sensitivity_at_x_eq_degree_in_S_pos {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : x ∈ S_pos f) :
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y) Finset.univ).card =
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S_pos f) Finset.univ).card := by
    -- Apply the lemma `g_val_neighbor_eq_iff_f_ne` to each neighbor `y` of `x`.
    have h_neighbor : ∀ y : Fin n → Bool, (hypercube_graph n).Adj x y → (f x ≠ f y ↔ y ∈ S_pos f) := by
      intros y hy_adj
      have h_g_eq : g_val f x = g_val f y ↔ f x ≠ f y := by
        exact g_val_neighbor_eq_iff_f_ne f x y hy_adj;
      unfold S_pos at *; aesop;
    exact congr_arg Finset.card ( Finset.ext fun y => by specialize h_neighbor y; aesop )

lemma sensitivity_at_x_eq_degree_in_S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : x ∈ S_neg f) :
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y) Finset.univ).card =
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S_neg f) Finset.univ).card := by
    unfold S_neg at *;
    congr! 2;
    ext y;
    constructor <;> intro h;
    · have := chi_univ_neighbor x y h.1; unfold g_val at *; aesop;
    · have := g_val_neighbor_eq_iff_f_ne f x y h.1; aesop;
```

This says: for a vertex x in S_pos, the number of adjacent y that flip f is exactly the number of adjacent y that stay inside S_pos. The corresponding lemma for S_neg is the same idea, just for the other level set.

## How it connects to neighboring concepts in the proof

1. **GVAL0 and LEVELSETS**: define g and show one level set (S_pos or S_neg) is larger than half the cube.
2. **NEIGH_RULE**: along any edge, g(x) = g(y) iff f(x) != f(y).
3. **DEG_SENS_LEVEL** (this atom): convert that edge-by-edge rule into a statement about degrees in the induced subgraph. Result: maxDegree of the large level set <= sensitivity.
4. **FULLCASE**: the spectral upper bound uses maxDegree; the spectral lower bound uses the large size of the level set; together they give sensitivity >= sqrt(n).

Without DEG_SENS_LEVEL, the spectral bound would be phrased in terms of graph degree, not sensitivity, so the proof would not close.

## Summary

DEG_SENS_LEVEL is the hinge between a local Boolean notion (sensitivity) and a graph-theoretic one (degree in an induced subgraph). It uses the g-transform and the neighbor rule to say: inside a g-level set, every internal edge is exactly a sensitivity edge. That makes the maximum degree of that induced subgraph a direct lower bound on sensitivity, which is exactly the form needed for the spectral argument that follows.
