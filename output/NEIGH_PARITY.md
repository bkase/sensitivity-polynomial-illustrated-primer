# NEIGH_PARITY: chi_univ flips sign along a hypercube edge

## Intuition and motivation
On the Boolean cube, an edge means "flip exactly one bit." Parity, however, is the even/odd count of 1s. Flipping one bit always changes that parity. So the global parity character chi_univ behaves like a perfect checkerboard coloring of the cube: every edge connects opposite colors.

This tiny fact is the hinge that links the g-transform to sensitivity. We define g by multiplying f with this parity pattern. Because parity flips on every edge, equality of g across an edge forces f to flip, and vice versa. That is exactly the NEIGH_RULE atom that follows.

Analogy: imagine a row of light switches. Parity is whether an even or odd number are ON. Flip exactly one switch and the parity must change. You cannot keep the same parity after a single flip.

## Plain-language statement
Let x and y be neighboring vertices in the hypercube (they differ in exactly one bit). Let chi_univ(x) be +1 if x has an even number of 1s and -1 if it has an odd number. Then:

```
chi_univ(x) = -chi_univ(y)
```

So neighbors always have opposite parity signs.

## How it shows up in the repo

### LaTeX definition of chi
From `sensitivity-polynomial.tex`:
```
chi_S(x) := (-1)^{x \\cdot S}
```
For S = all coordinates, this becomes:
```
chi_univ(x) = (-1)^{|x|}
```
where |x| is the number of 1s in x.

### Lean statement of the lemma
From `sensitivity.lean`:
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
This is exactly the NEIGH_PARITY atom: adjacency in the hypercube forces the parity character on all bits to flip sign.

## Why the parity must flip (short proof)
If x and y differ in exactly one bit, then the number of 1s in y is either |x| + 1 or |x| - 1. So:

```
chi_univ(y) = (-1)^{|y|}
            = (-1)^{|x|+1}  or  (-1)^{|x|-1}
            = -(-1)^{|x|}
            = -chi_univ(x)
```

## A tiny example (n = 3)
Let x = 010. It has one 1, so chi_univ(x) = -1 (odd).
Its neighbor y = 011 differs in one bit, has two 1s, so chi_univ(y) = +1 (even).
They are opposite, as the lemma says.

## Where NEIGH_PARITY sits in the proof DAG
From `history/breakdown.md`:

**What NEIGH_PARITY represents**
- One parity fact about the cube: chi_univ flips sign along an edge.

**Depends on**
- **BC1** (neighbor relation / hypercube graph), because you need "x ~ y" to talk about edges.
- **CHI0** (parity characters), because chi_univ is a special case of chi_S.

**Used by**
- **NEIGH_RULE** (neighbor rule), which combines the sign flip with the definition of g.
- Downstream: **DEG_SENS_LEVEL** uses NEIGH_RULE to turn sensitivity into degree in a level-set subgraph.

## Connection to neighboring atoms

### CHI0 (prerequisite)
NEIGH_PARITY is a one-line consequence of CHI0 when S is the full coordinate set. It is the "checkerboard" property of chi_univ on the hypercube.

### GVAL0 and NEIGH_RULE (what this enables next)
Lean defines:
```lean
def g_val {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℝ :=
  (if f x then -1 else 1) * chi Finset.univ x
```
where `(if f x then -1 else 1)` is +1 for false and -1 for true. If x ~ y, then:

```
g_val(y) = sign(f(y)) * chi_univ(y)
         = sign(f(y)) * (-chi_univ(x))
```

So:
```
g_val(x) = g_val(y)  <->  sign(f(x)) = -sign(f(y))  <->  f(x) != f(y)
```
This is the NEIGH_RULE atom. NEIGH_PARITY is the single input that makes the algebra work.

## Self-contained takeaway
NEIGH_PARITY says: in the hypercube, flipping one bit flips the global parity. Formally,
```
x ~ y  ->  chi_univ(x) = -chi_univ(y)
```
This checkerboard property is the key that turns the parity-twisted function g into a sensitivity-counting tool on edges.
