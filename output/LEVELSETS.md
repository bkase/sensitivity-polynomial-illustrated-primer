# LEVELSETS: level sets of g and the "one is bigger than half" fact

## Intuition and motivation
At this point in the proof we already have a function g that only takes values +1 or -1, and we know its average (sum) is not zero (from GVAL0). That is a purely algebraic or Fourier-sourced fact. But the next steps need a large *subset* of the hypercube to feed into graph and spectral arguments. LEVELSETS is the bridge: it converts "nonzero average" into "one level set has more than half the vertices."

Think of g as a vote on each vertex: +1 or -1. If the total vote is not zero, then there are strictly more +1 votes than -1 votes (or vice versa). So the set of vertices with g = +1 must be bigger than half of all vertices, or the set with g = -1 must be bigger than half. That is the only fact we need, but it is crucial: it guarantees a large induced subgraph to which the spectral bound applies.

## Plain-language definition of a level set
A "level set" just means "the set of inputs where the function takes a particular value."

For a +/-1-valued function g on the hypercube {0,1}^n, there are exactly two level sets:

```
S_pos = { x : g(x) = +1 }
S_neg = { x : g(x) = -1 }
```

These two sets are disjoint and cover the whole cube. So their sizes add up to 2^n.

## The key combinatorial fact
Because g(x) is always +1 or -1, the sum of g over all vertices is exactly the difference between the two level-set sizes:

```
Sum_x g(x) = |S_pos| - |S_neg|
```

So:
- If Sum_x g(x) != 0, then |S_pos| != |S_neg|.
- Since |S_pos| + |S_neg| = 2^n, the larger one must be bigger than half:

```
|S_pos| > 2^(n-1)  OR  |S_neg| > 2^(n-1)
```

That is the entire LEVELSETS atom.

### A quick analogy
Imagine 2^n coins laid out on a table, each labeled +1 or -1. If the total sum is not zero, you must have more +1 coins than -1 coins (or vice versa). That simple counting fact is the whole argument.

## Where LEVELSETS sits in the proof graph
From `history/breakdown.md`:

What LEVELSETS represents
- "Level sets S_pos/S_neg; one has size > 2^(n-1)."

Depends on
- GVAL0 (we need the nonzero sum of g to force an imbalance).

Used by
- DEG_SENS_LEVEL (the large level set is where we compare degree to sensitivity).
- HUANG_SUB_LOWER (the spectral lower bound needs a subset larger than half).

## How it shows up in the LaTeX notes
The notes define g by twisting f with parity, then define the +1 level set:

```tex
let g(x) := f(x) \chi_{[n]}.
Then S := { x | g(x) = 1 }.
```

Right after that, there is a lemma saying E(g) != 0. LEVELSETS is the combinatorial consequence of that lemma: if the expectation is not zero, then S (or its complement) has size strictly larger than half of the cube.

## How it is formalized in Lean
Lean makes the level sets explicit as `S_pos` and `S_neg`, proves they partition the cube, and then derives the size imbalance.

```lean
def g_val {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℝ :=
  (if f x then -1 else 1) * chi Finset.univ x

def S_pos {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.filter (fun x => g_val f x = 1) Finset.univ

def S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.filter (fun x => g_val f x = -1) Finset.univ

lemma exists_large_level_set {n : ℕ} (f : (Fin n → Bool) → Bool) (h_deg : degree f = n) (hn : n ≠ 0) :
  (S_pos f).card > 2^(n-1) ∨ (S_neg f).card > 2^(n-1) := by
    -- Since sum g_val ≠ 0, we have |S_pos| ≠ |S_neg|.
    have h_card_ne : (S_pos f).card ≠ (S_neg f).card := by
      have h_card_ne : (Finset.sum Finset.univ (g_val f)) = (S_pos f).card - (S_neg f).card := by
        -- By definition of $g_val$, we can split the sum into the sum over $S_pos$ and the sum over $S_neg$.
        have h_split_sum : Finset.sum Finset.univ (g_val f) = Finset.sum (S_pos f) (fun x => g_val f x) + Finset.sum (S_neg f) (fun x => g_val f x) := by
          rw [ ← Finset.sum_union ];
          · rw [ S_pos_union_S_neg ];
          · exact S_pos_disjoint_S_neg f;
        rw [ h_split_sum, Finset.sum_congr rfl fun x hx => show g_val f x = 1 by exact Finset.mem_filter.mp hx |>.2, Finset.sum_congr rfl fun x hx => show g_val f x = -1 by exact Finset.mem_filter.mp hx |>.2 ] ; norm_num;
        ring;
      have := g_val_sum_ne_zero f h_deg hn; aesop;
    -- Since $|S_pos| + |S_neg| = 2^n$, we have $|S_pos| + |S_neg| = 2 * 2^{n-1}$.
    have h_card_sum : (S_pos f).card + (S_neg f).card = 2 * 2 ^ (n - 1) := by
      have h_card_sum : (S_pos f).card + (S_neg f).card = (Finset.univ : Finset (Fin n → Bool)).card := by
        rw [ ← Finset.card_union_of_disjoint ( S_pos_disjoint_S_neg f ), S_pos_union_S_neg ];
      cases n <;> simp_all +decide [ pow_succ' ];
    grind
```

The proof in Lean explicitly uses the identity

```
Sum g_val = |S_pos| - |S_neg|
```

and the partition identity

```
|S_pos| + |S_neg| = 2^n.
```

## How it connects to neighboring concepts
- From GVAL0: We know Sum g_val != 0. LEVELSETS turns that into a large subset of vertices.
- To DEG_SENS_LEVEL: Once we choose the larger level set, we look at the induced subgraph on that set, and show its degrees match sensitivity counts.
- To HUANG_SUB_LOWER: The spectral interlacing bound requires an induced subgraph on more than half the vertices. LEVELSETS provides exactly that size guarantee.

## Self-contained takeaway
LEVELSETS is the simple but crucial counting step:

If a +/-1-valued function on the hypercube has nonzero average, then it must have more +1 inputs than -1 inputs (or vice versa). Because there are 2^n total inputs, one of the two level sets is strictly larger than 2^(n-1). This is the combinatorial entry point that lets the proof move from Fourier imbalance to large induced subgraphs and, later, spectral bounds on sensitivity.
