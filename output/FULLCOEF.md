# FULLCOEF: full degree forces the top Fourier coefficient to be nonzero

## Intuition and motivation
Think of a normal polynomial in n variables. If a polynomial has degree n, then there is at least one term that uses all n variables at once (like x1*x2*...*xn). If there were no such term, the degree would be smaller.

FULLCOEF is the same idea, but for the Fourier expansion of a boolean function. The proof needs this to show that a transformed function g is *imbalanced* (its average is not zero). That imbalance later implies one of the two level sets of g is larger than half the cube, which is the key combinatorial lever for the sensitivity lower bound.

## What FULLCOEF says (plain language)
- A boolean function f on n bits has a Fourier expansion indexed by subsets S of {1,...,n}.
- The **degree** of f is the largest size |S| with nonzero Fourier coefficient f_hat(S).
- If degree(f) = n ("full degree"), then the coefficient on the *full set* S = {1,...,n} is nonzero.

There is only one subset of size n: the full set. So "some coefficient of size n is nonzero" is the same as "the top coefficient at S = univ is nonzero." That is exactly FULLCOEF.

## Where it sits in the proof graph
From `history/breakdown.md`:
- **Represents:** "Full-degree witness: degree(f)=n implies f_hat(univ) != 0."
- **Depends on:** **DEG0** (the definition of degree from Fourier support).
- **Used by:** **GVAL0** (the g-transform step that shows g has nonzero mean).

So FULLCOEF is the tiny hinge between a *structural* property (full degree) and a *numerical* property (a specific coefficient is nonzero).

## The core idea with an analogy
Imagine you have a "recipe" for f written as a sum of parity features (the Fourier basis). Each feature corresponds to a subset S. The size of S is the "order" of that feature.

- If the recipe says the highest-order feature uses all n ingredients, then the coefficient on that feature must be nonzero.
- Otherwise, the highest-order feature would actually use fewer ingredients, contradicting the claim that the degree is n.

That's FULLCOEF in one sentence.

## How it appears in the LaTeX notes
In `sensitivity-polynomial.tex`, the lemma "E(g) != 0" relies on the fact that the coefficient of the parity character chi_[n] is nonzero:

```
Lemma: E(g) != 0.
Proof: The transformation f -> g is a bijection between monomials of f and g.
The monomial 1 in g comes from the monomial chi_[n] in f, which we know has a nonzero coefficient.
E(g) is simply this coefficient.
```

That "we know has a nonzero coefficient" is exactly FULLCOEF.

## How it appears in the Lean formalization
The Lean file defines chi, Fourier coefficients, and degree like this:

```lean
/-
chi_S(x) is (-1)^(x \cdot S), which is 1 if the number of indices in S where x is true is even, and -1 otherwise.
-/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  if (Finset.filter (fun i => x i) S).card % 2 = 0 then 1 else -1

/-
The Fourier coefficient f_hat(S) is the expectation of f(x) * chi_S(x). The degree of f is the size of the largest set S such that f_hat(S) is non-zero.
-/
noncomputable def fourier_coeff {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℝ :=
  (Finset.sum Finset.univ (fun x => (if f x then 1 else 0) * chi S x)) / 2^n

noncomputable def degree {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.sup (Finset.filter (fun S => fourier_coeff f S ≠ 0) Finset.univ) Finset.card
```

Then the proof of `g_expectation_nonzero` uses full degree to produce a subset S of size n with nonzero coefficient, and concludes S must be `univ`:

```lean
/-
$\EE(g) \neq 0$
-/
theorem g_expectation_nonzero {n : ℕ} (f : (Fin n → Bool) → Bool) (h_deg : degree f = n) (hn : n ≠ 0) :
  let g := fun x => (if f x then 1 else 0) * chi Finset.univ x
  (Finset.sum Finset.univ g) ≠ 0 := by
    have h_fourier_coeff : ∃ S : Finset (Fin n), fourier_coeff f S ≠ 0 ∧ S.card = n := by
      contrapose! h_deg;
      refine' ne_of_lt ( lt_of_le_of_lt ( Finset.sup_le _ ) _ );
      exacts [ n - 1, fun S hS => Nat.le_sub_one_of_lt <| lt_of_le_of_ne ( le_trans ( Finset.card_le_univ _ ) <| by simp ) <| h_deg S <| by simpa using hS, Nat.pred_lt hn ];
    obtain ⟨ S, hS₁, hS₂ ⟩ := h_fourier_coeff; simp_all +decide [ fourier_coeff ] ;
    have := Finset.eq_of_subset_of_card_le ( Finset.subset_univ S ) ; aesop;
```

That is the formalized FULLCOEF step.

## Why this matters downstream (connection to GVAL0)
The next atom (GVAL0) defines a transformed function:

```lean
let g := fun x => (if f x then 1 else 0) * chi Finset.univ x
```

The average of g is exactly the Fourier coefficient f_hat(univ). So FULLCOEF tells us:

- f_hat(univ) != 0
- therefore average(g) != 0
- therefore g is imbalanced (more +1s than -1s or vice versa)

That imbalance is what creates a large level set, which then connects to sensitivity via the hypercube graph.

## Minimal prerequisites (what you need to understand FULLCOEF)
- **CHI0**: chi_S(x) is a parity function over subset S.
- **FOURIER0**: f_hat(S) measures correlation of f with chi_S.
- **DEG0**: degree(f) is the largest |S| with f_hat(S) != 0.

Once you accept those definitions, FULLCOEF is the simple combinatorial observation: "if the max size is n, the only candidate is the full set."
