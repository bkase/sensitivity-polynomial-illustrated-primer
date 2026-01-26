# DEG_FROM_TOP: Top coefficient implies full degree

## Intuition and motivation

When you do Fourier analysis on a Boolean function, you get a sum of "parity
monomials" (the chi_S terms). The *degree* is the size of the largest subset
S that appears with a nonzero coefficient. So a natural way to prove a function
has *full* degree is to show that the coefficient of the biggest possible term
is not zero.

Think of an ordinary polynomial. If the coefficient of x^n is nonzero, then
the polynomial really has degree n. The Fourier expansion is similar: the
"top coefficient" is the coefficient of the parity term involving *all*
variables. If that coefficient is nonzero, the function has full degree.

This is exactly what DEG_FROM_TOP formalizes. It is a tiny but crucial bridge
in the reduction step: once we restrict to a smaller subcube, we can detect
full degree there just by checking the top coefficient.

## What DEG_FROM_TOP says (plain language)

For a Boolean function on n variables:

- If the Fourier coefficient on the full set of variables is nonzero,
  then the degree of the function is exactly n.

For a restriction g = f|_{S,z} on k = |S| variables:

- If g's Fourier coefficient on *its* full set (called `univ` in Lean) is
  nonzero, then degree(g) = k.

So: **"Top coefficient nonzero" is equivalent to "full degree."**

## Minimal prerequisites

You only need:

- **FOURIER0**: Fourier coefficients f_hat(S) for subsets S.
- **DEG0**: degree(f) is the largest |S| with f_hat(S) != 0.

In the restriction pipeline, this lemma is fed by:

- **EXIST_TOP**: there exists a restriction with top coefficient != 0.

From `history/breakdown.md` (the proof DAG):

- **What DEG_FROM_TOP depends on**: **FOURIER0**, **DEG0**.
- **What depends on DEG_FROM_TOP**: **REDUCE** (the general-degree reduction).

## Where it appears in the repo

### Lean (sensitivity.lean)
The lemma is written explicitly:

```lean
lemma degree_eq_n_of_fourier_coeff_univ_ne_zero {n : ℕ} (f : (Fin n → Bool) → Bool) (h : fourier_coeff f Finset.univ ≠ 0) :
  degree f = n := by
    refine' le_antisymm _ _;
    · exact Finset.sup_le fun S hS => Nat.le_trans ( Finset.card_le_univ _ ) ( by norm_num );
    · refine' le_trans _ ( Finset.le_sup <| Finset.mem_filter.mpr ⟨ Finset.mem_univ Finset.univ, h ⟩ );
      norm_num
```

And it is used in the reduction step to prove the restricted function has full
degree:

```lean
-- By `degree_eq_n_of_fourier_coeff_univ_ne_zero`, degree g = k.
have h_deg_g : degree (restriction f S z) = S.card := by
  have := degree_eq_n_of_fourier_coeff_univ_ne_zero ( restriction f S z ) hz; aesop;
```

### LaTeX (sensitivity-polynomial.tex)
The notes do not name the lemma, but they use its idea when they say:

> "Pick a term T in f of maximum degree and restrict to the subcube Q_T."

Once you restrict to T, the "top term" in that smaller cube is nonzero, so the
restricted function has full degree in its own dimension.

## Why the statement is true (informal proof)

Let f be a Boolean function on n variables. Its Fourier expansion is

f(x) = sum_{S subseteq [n]} f_hat(S) * chi_S(x)

By definition:

degree(f) = max{|S| : f_hat(S) != 0}.

Now assume the *top coefficient* is nonzero:

f_hat([n]) != 0.

Then two things are immediate:

1) The degree is **at least n**, because there is a nonzero coefficient on a
   set of size n.
2) The degree is **at most n**, because you cannot have a subset larger than
   [n].

Therefore degree(f) = n.

The restricted version is the same argument, just with "n" replaced by
k = |S| (the number of free variables in the restriction).

## How it connects to neighboring concepts

### Connection to FOURIER_AVG and EXIST_TOP
FOURIER_AVG says the original coefficient f_hat(S) is the average of the top
coefficients of the restrictions on S. If that average is nonzero, then some
restriction has a nonzero top coefficient (EXIST_TOP). DEG_FROM_TOP then
converts that fact into "this restriction has full degree."

### Connection to FULLCASE (full-degree theorem)
FULLCASE proves sensitivity bounds *only* for full-degree functions. So we
need to get full degree after restriction. DEG_FROM_TOP is the exact step
that makes that legal:

f_hat(univ) != 0  ==>  degree = number of variables.

### Connection to REDUCE
The overall reduction is:

1) Pick a max-degree set S (DEG_WITNESS).
2) Use Fourier averaging to find a restriction with nonzero top coefficient
   (FOURIER_AVG + EXIST_TOP).
3) Apply DEG_FROM_TOP to show the restriction has full degree.
4) Apply FULLCASE to that restricted function.
5) Lift the bound back to f (SENS_MONO).

DEG_FROM_TOP is the link between Step 2 and Step 3.

## Tiny example

Suppose g(x1, x2, x3) has Fourier expansion with a nonzero coefficient on
chi_{1,2,3}. Then:

- There is a nonzero term of size 3.
- No term can be larger than size 3.
- So degree(g) = 3.

That is exactly the logic of DEG_FROM_TOP.

## Summary takeaway

DEG_FROM_TOP is the "leading coefficient test" for Boolean Fourier degree.
If the coefficient on the full set of variables is nonzero, the function
must have full degree. This is the key certificate that lets the proof switch
from an arbitrary function to a full-degree function after restriction.
