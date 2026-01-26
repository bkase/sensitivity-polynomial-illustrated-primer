# GVAL0: the g_val transform and its nonzero-sum property

## Intuition and motivation
At this stage of the proof, we have a *Fourier* fact: full degree means the top Fourier coefficient is nonzero (FULLCOEF). But the next step needs a *combinatorial* fact about the hypercube: a large subset of vertices where a certain sign pattern is constant. GVAL0 is the bridge.

The idea is to twist the function by the global parity pattern (a checkerboard on the cube). If the top Fourier coefficient is nonzero, then after this twist the function is no longer perfectly balanced between +1 and -1. That imbalance is exactly what lets us say "one of the two level sets must be bigger than half."

Analogy: imagine a checkerboard with black/white squares. If you paint each square either +1 or -1, and then flip the sign on every black square, you get a new coloring. GVAL0 says: if the original coloring has a certain "global parity signal," the flipped coloring cannot be perfectly balanced. There will be more +1s than -1s (or vice versa).

## The definition in plain language
We work on the Boolean cube: each input is a bitstring x in {0,1}^n.

1. **Parity pattern** (from CHI0):  
   `chi_univ(x)` is +1 if x has an even number of 1s, and -1 if it has an odd number.

2. **Turn f into a sign**:  
   If `f(x)` is Boolean, define
   ```
   sign(f(x)) = 1  if f(x) = false
              = -1 if f(x) = true
   ```
   This is the same as `1 - 2 * 1_{f(x)=true}` or `(-1)^{f(x)}`.

3. **Twist by parity**:  
   ```
   g_val(x) = sign(f(x)) * chi_univ(x)
   ```
   So g_val(x) is always +1 or -1.

This transform is the "g" in the LaTeX notes, but written in a way that makes the sign-flip explicit.

## The key property (why we need it)
If f has full degree (degree(f) = n) and n != 0, then:

```
sum_x g_val(x) != 0
```

Why does that matter? Because for a +/-1-valued function, the sum is literally:

```
sum_x g_val(x) = (# of +1) - (# of -1)
```

So "sum != 0" means the +1 and -1 counts are not equal. This is exactly the imbalance that the next atom (LEVELSETS) turns into a "large level set" statement.

### How the proof connects Fourier to this sum
Use the identity:
```
g_val(x) = (1 - 2 * 1_{f(x)=true}) * chi_univ(x)
         = chi_univ(x) - 2 * (1_{f(x)=true} * chi_univ(x))
```

Summing over all x:

```
sum_x g_val(x) = sum_x chi_univ(x) - 2 * sum_x (1_{f(x)=true} * chi_univ(x))
```

For n != 0, the parity pattern is perfectly balanced, so:
```
sum_x chi_univ(x) = 0
```

Thus:
```
sum_x g_val(x) = -2 * sum_x (1_{f(x)=true} * chi_univ(x))
```

The right-hand side is (up to the 2^n normalization) exactly the top Fourier coefficient f_hat(univ). FULLCOEF says that coefficient is nonzero, so the sum is nonzero. That is the one-line reason GVAL0 works.

## Where GVAL0 sits in the proof graph
From `history/breakdown.md`:

**What GVAL0 represents**
- The g_val transform plus its one key property: "full degree implies g_val has nonzero mean."

**Depends on**
- **BC0** (the Boolean cube, so we can sum over all x)
- **CHI0** (the parity character chi_univ)
- **FULLCOEF** (full degree -> top Fourier coefficient nonzero)

**Used by**
- **LEVELSETS** (nonzero sum -> one of S_pos/S_neg is larger than half)
- **NEIGH_RULE** (relates g_val equality along an edge to f flipping)

## How it appears in the LaTeX notes
In `sensitivity-polynomial.tex`, the transform is introduced as:

```
let g(x) := f(x) \chi_{[n]}.
```

and the key lemma is:

```
Lemma: E(g) != 0.
```

That lemma is exactly the "nonzero sum" property, phrased in expectation form.

## How it appears in the Lean formalization
Lean names the transform `g_val` and proves the nonzero-sum lemma:

```lean
def g_val {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℝ :=
  (if f x then -1 else 1) * chi Finset.univ x

lemma g_val_sum_ne_zero {n : ℕ} (f : (Fin n → Bool) → Bool) (h_deg : degree f = n) (hn : n ≠ 0) :
  Finset.sum Finset.univ (g_val f) ≠ 0 := by
    unfold g_val;
    -- By definition of `g_val`, we can rewrite it in terms of `chi` and `f`.
    have hg_val : ∑ x : Fin n → Bool, (if f x then -1 else 1) * chi Finset.univ x = -2 * ∑ x : Fin n → Bool, (if f x then 1 else 0) * chi Finset.univ x + ∑ x : Fin n → Bool, chi Finset.univ x := by
      rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring;
    -- Since $\sum_{x} \chi_{Finset.univ}(x) = 0$ for $n \neq 0$, we have:
    have h_sum_chi : ∑ x : Fin n → Bool, chi Finset.univ x = 0 := by
      unfold chi;
      -- Let's simplify the sum $\sum_{x : Fin n → Bool} (-1)^{\text{card}(\{i | x i = true\})}$.
      have h_sum_simplified : ∑ x : Fin n → Bool, (-1 : ℝ) ^ (Finset.card (Finset.filter (fun i => x i) Finset.univ)) = ∏ i : Fin n, (∑ x_i : Bool, (-1 : ℝ) ^ (if x_i then 1 else 0)) := by
        rw [ Finset.prod_sum ];
        refine' Finset.sum_bij ( fun x _ => fun i _ => x i ) _ _ _ _ <;> simp +decide;
        · simp +decide [ funext_iff ];
        · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), rfl ⟩;
        · intro a; rw [ Finset.prod_ite ] ; aesop;
      convert h_sum_simplified using 1;
      · exact Finset.sum_congr rfl fun x hx => by rcases Nat.mod_two_eq_zero_or_one ( Finset.card ( Finset.filter ( fun i => x i = true ) Finset.univ ) ) with h | h <;> rw [ ← Nat.mod_add_div ( Finset.card ( Finset.filter ( fun i => x i = true ) Finset.univ ) ) 2 ] <;> norm_num [ pow_add, pow_mul, h ] ;
      · norm_num [ Finset.prod_eq_zero_iff ];
        rw [ zero_pow hn ];
    have := g_expectation_nonzero f h_deg hn; aesop;
```

This is the formal counterpart of the LaTeX "E(g) != 0" lemma.

## Connection to the neighboring atoms

### LEVELSETS (what happens next)
Define:
```
S_pos = { x | g_val(x) = 1 }
S_neg = { x | g_val(x) = -1 }
```
Since `sum g_val = |S_pos| - |S_neg|`, a nonzero sum forces one set to be larger than half. That is the LEVELSETS atom.

### NEIGH_RULE (how it links to sensitivity)
Another nearby fact (NEIGH_RULE) uses the parity flip along edges (NEIGH_PARITY) to show:
```
g_val(x) = g_val(y)  iff  f(x) != f(y)
```
for neighboring vertices x ~ y. This turns statements about g_val on edges into statements about sensitivity.

## Self-contained takeaway
GVAL0 defines a simple sign-twisted version of f:

```
g_val(x) = (-1)^{f(x)} * chi_univ(x)
```

If f has full degree, then the top Fourier coefficient is nonzero, which forces the average (sum) of g_val to be nonzero. This is the crucial "imbalance" step: it is the only place where a Fourier fact is converted into a combinatorial count, and it sets up the large level-set and sensitivity arguments that follow.
