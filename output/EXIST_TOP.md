# EXIST_TOP: Finding a restriction with a nonzero top coefficient

## Intuition and motivation (why we need this)
The overall proof reduces the general case ("any degree") to the full-degree case.
To do that, we pick a Fourier term S that witnesses the degree of f, then we
"freeze" all variables outside S to get a smaller function on just S. The
full-degree theorem only applies if the restricted function has its *top*
Fourier coefficient nonzero (the coefficient on the parity of all remaining
variables). EXIST_TOP is the tiny but crucial step that guarantees *some*
restriction has that nonzero top coefficient.

In short: if a certain average is nonzero, at least one term in that average
must be nonzero.

## What EXIST_TOP says (informal)
Let f be a Boolean function on n bits, and let S be a set of coordinates with
Fourier coefficient \hat{f}(S) != 0. For each assignment z to the n variables,
freeze f outside S according to z, giving a restricted function f|_{S,z} that
only depends on the variables in S. Then:

    If \hat{f}(S) != 0, there exists some z such that
    the top coefficient of f|_{S,z} is nonzero.

Here "top coefficient" means the Fourier coefficient of f|_{S,z} on the full
set of its remaining variables (called "univ" in the Lean code).

## The key averaging identity it relies on
The previous atom FOURIER_AVG gives this identity:

    \hat{f}(S) = (1 / 2^n) * sum_{z in {0,1}^n} \widehat{f|_{S,z}}(U)

where U is the "all variables" set of the restricted function. This is just an
average of the top coefficients across all restrictions.

If that average is nonzero, then not all the terms can be zero. Therefore,
at least one z makes \widehat{f|_{S,z}}(U) != 0. That is EXACTLY EXIST_TOP.

## Plain-language analogy
Imagine you have a list of numbers, and their average is 3. Then at least one
number in the list must be nonzero (in fact, not all can be zero). EXIST_TOP
is that logic, but applied to a list of Fourier coefficients coming from all
possible restrictions.

## How it connects to neighboring concepts
Depends on:
- DEG_WITNESS: gives a set S with \hat{f}(S) != 0.
- FOURIER_AVG: expresses \hat{f}(S) as the average of the top coefficients of
  all restrictions f|_{S,z}.

Used by:
- DEG_FROM_TOP: once we find a restriction with nonzero top coefficient, we
  know that restriction has full degree (degree = |S|).
- REDUCE: combines that full-degree restriction with the full-degree theorem
  and sensitivity monotonicity to finish the reduction.

So EXIST_TOP is the "existence extraction" bridge between averaging and
"there is a good restriction."

## Lean (ASCII-ified) snippet and explanation
This is the lemma in the Lean file, written in ASCII to keep it readable:

```lean
lemma exists_restriction_fourier_coeff_univ_ne_zero {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (hS : fourier_coeff f S ≠ 0) :
  ∃ z : Fin n → Bool, fourier_coeff (restriction f S z) Finset.univ ≠ 0 := by
    rw [ fourier_coeff_restriction_avg ] at hS;
    exact not_forall.mp fun h => hS <| by rw [ Finset.sum_eq_zero fun _ _ => h _ ] ; norm_num;
```

The proof is literally two moves:
1) Rewrite hS using the averaging identity `fourier_coeff_restriction_avg`.
2) If every term in the sum were zero, the sum (and hence the average) would be
   zero, contradicting hS. Therefore some term is nonzero.

## Math snippet (same idea)
```text
\hat{f}(S) = E_z[ \widehat{f|_{S,z}}(U) ].
If \hat{f}(S) != 0, then exists z with \widehat{f|_{S,z}}(U) != 0.
```

## Takeaway
EXIST_TOP is not a deep Fourier fact; it is a logical extraction step. It turns
an averaged nonzero quantity into a concrete witness z. That witness is what
lets the proof drop from "general degree" to "full degree" on a smaller cube.
