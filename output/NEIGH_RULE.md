# NEIGH_RULE: the neighbor rule linking g and f

## Intuition and motivation

The proof wants to translate a question about **sensitivity** (where does f flip when you move to a neighboring vertex in the hypercube) into a **graph degree** problem on a large subset of vertices. To do this, it defines a new function g by multiplying f by a checkerboard-like sign based on parity. On a hypercube, **parity flips on every edge**. So when you move to a neighbor, the parity sign changes automatically. That means:

- If f stays the same across an edge, g flips.
- If f flips across an edge, g stays the same.

The NEIGH_RULE is exactly this idea, written as a precise equivalence. It is the bridge that lets the proof count sensitivity by counting neighbors that stay in the same g-level set.

## The concept in plain language

Think of the n-dimensional hypercube as a massive checkerboard. Every vertex has a parity color (black/white), and **every edge connects opposite colors**. Now define g(x) to be f(x) multiplied by that parity color. So g is f “viewed through a checkerboard filter.”

Because the checkerboard color flips on every step:

- If f(x) and f(y) are the same, then g(x) and g(y) must be opposite.
- If f(x) and f(y) are different, then g(x) and g(y) become the same.

So along a neighbor edge, “g equal” is exactly the same as “f different.” That is NEIGH_RULE.

## Formal statement (math)

Let x and y be neighbors in the hypercube (they differ in exactly one bit), and let chi_univ be the parity character. Define

```
chi_univ(x) = (-1)^(number of 1s in x)

g(x) = f_sign(x) * chi_univ(x)
```

Here f_sign(x) is the +/-1 encoding of the Boolean f(x) (Lean uses `(if f x then -1 else 1)` for that).

Then NEIGH_RULE says:

```
x ~ y  ==>  g(x) = g(y)  <->  f(x) != f(y)
```

The key step is the parity flip on edges:

```
chi_univ(x) = -chi_univ(y)
```

So

```
g(x) = f_sign(x) * chi_univ(x)
     = f_sign(x) * (-chi_univ(y))
```

Thus g(x) = g(y) happens exactly when f_sign(x) = -f_sign(y), i.e., when f(x) and f(y) differ.

## Where it appears in the Lean code

Definition of g (named `g_val`):

```lean
def g_val {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℝ :=
  (if f x then -1 else 1) * chi Finset.univ x
```

Parity flips on neighbors:

```lean
lemma chi_univ_neighbor {n : ℕ} (x y : Fin n → Bool) (h_adj : (hypercube_graph n).Adj x y) :
  chi Finset.univ x = -chi Finset.univ y := by
    -- Since x and y differ by exactly one bit, their parities are opposite.
    have h_parity : (Finset.filter (fun i => x i) Finset.univ).card % 2 ≠ (Finset.filter (fun i => y i) Finset.univ).card % 2 := by
      have h_parity : (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1 := by
        exact (hypercube_graph_adj x y).mp h_adj;
      -- Since x and y differ by exactly one bit, the number of 1s in x and y differ by 1.
      have h_diff : (Finset.filter (fun i => x i = true) Finset.univ).card + (Finset.filter (fun i => y i = true) Finset.univ).card = (Finset.filter (fun i => x i ≠ y i) Finset.univ).card + 2 * (Finset.filter (fun i => x i = true ∧ y i = true) Finset.univ).card := by
        rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
        rw [ Finset.card_filter ];
        rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext i ; by_cases hi : x i <;> by_cases hj : y i <;> simp +decide [ hi, hj ] ;
      omega;
    unfold chi; aesop;
```

The neighbor rule itself:

```lean
lemma g_val_neighbor_eq_iff_f_ne {n : ℕ} (f : (Fin n → Bool) → Bool) (x y : Fin n → Bool) (h_adj : (hypercube_graph n).Adj x y) :
  g_val f x = g_val f y ↔ f x ≠ f y := by
    have h_univ_neighbor : chi Finset.univ x = -chi Finset.univ y := by
      exact chi_univ_neighbor x y h_adj;
    unfold g_val;
    cases f x <;> cases f y <;> simp +decide [ * ];
    · unfold chi at *;
      split_ifs at * <;> norm_num at *;
    · unfold chi; split_ifs <;> norm_num;
```

## What NEIGH_RULE depends on (from breakdown.md)

- **NEIGH_PARITY**: neighbors in the hypercube have opposite parity, i.e., `chi_univ(x) = -chi_univ(y)`.
- **GVAL0**: definition of the g-transform (the signed version of f using parity).

These two facts combine directly: g is defined using parity, and parity flips on every edge, so equality of g along edges is equivalent to a flip of f.

## What depends on NEIGH_RULE

- **DEG_SENS_LEVEL**: This later step converts sensitivity into degree inside an induced subgraph on a large level set of g. The rule gives the exact equivalence needed: for a vertex in the `g = 1` level set, the neighbors where f flips are exactly the neighbors that stay in the same g-level set. So sensitivity becomes “degree in the induced graph.”

## How it connects to the proof flow

1. **GVAL0** defines g and shows it has a nonzero average when degree(f) = n.
2. **LEVELSETS** uses that nonzero average to show one of the level sets of g is large.
3. **NEIGH_RULE** says edges where f flips are exactly edges where g stays the same.
4. **DEG_SENS_LEVEL** uses that to reinterpret sensitivity as degree inside the large level set.

So NEIGH_RULE is the critical translation step: it turns “f changes across an edge” into “stay inside a g-level set,” which makes the spectral graph argument possible.

## Prerequisites (lightweight)

You only need a few ideas:

- The **hypercube graph**: vertices are bitstrings, neighbors differ in one bit.
- The **parity character** `chi_univ`: alternates between +1 and -1 on neighbors.
- The **g-transform**: multiply f (encoded as +/-1) by that parity sign.

Everything in NEIGH_RULE is just the algebraic interaction of those three ingredients.
