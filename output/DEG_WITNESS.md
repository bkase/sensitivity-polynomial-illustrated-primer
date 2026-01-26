# DEG_WITNESS: Degree witness set S

## Intuition and motivation

The degree of a Boolean function is defined as a single number: the largest
"interaction size" that shows up in its Fourier expansion. But a number alone
is not enough to drive the proof. Later steps need an actual subset of
coordinates to restrict to and analyze. DEG_WITNESS is the bridge: it says
there exists a specific set S of coordinates that *achieves* the degree. In
other words, the degree is not just a max in theory; there is a concrete
"top-degree term" you can point to.

Analogy: Think of a recipe with many ingredients, where some steps combine
several ingredients at once. The degree is the largest number of ingredients
used in any single step. DEG_WITNESS says there really is a step that uses that
many ingredients. That lets you focus on exactly those ingredients in the next
part of the proof.

## What DEG_WITNESS is (plain-language definition)

A Boolean function f on n bits can be expanded in the parity basis (the
chi_S functions). Each subset S of coordinates has a Fourier coefficient
f_hat(S). The degree is defined as:

- the largest size |S| where f_hat(S) is nonzero.

DEG_WITNESS is the existence statement:

- there exists a subset S with |S| = degree(f) and f_hat(S) != 0.

So DEG_WITNESS is the formal way of saying "pick a top-degree term." It does
not compute S; it just guarantees S exists.

## Prerequisites (minimal)

You only need these concepts:

- CHI0: parity characters chi_S(x), the building blocks of the Fourier basis.
- FOURIER0: Fourier coefficients f_hat(S) = E_x[f(x) * chi_S(x)].
- DEG0: degree(f) is the maximum |S| with f_hat(S) != 0.

DEG_WITNESS is a direct consequence of DEG0 plus finiteness (there are only
finitely many subsets S).

## Where this appears in the repo

### LaTeX (sensitivity-polynomial.tex)
The notes phrase it informally:

"Pick a term T in f of maximum degree and restrict to the subcube Q_T."

That "term T" is exactly the degree witness set S.

### Lean (sensitivity.lean)
The degree definition is a supremum over all subsets with nonzero coefficient:

```lean
noncomputable def degree {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.sup (Finset.filter (fun S => fourier_coeff f S ≠ 0) Finset.univ) Finset.card
```

Later, the proof explicitly extracts a witness from this supremum:

```lean
obtain ⟨k, hk⟩ : ∃ k : ℕ, k = degree f ∧ ∃ S : Finset (Fin n), S.card = k ∧ fourier_coeff f S ≠ 0 := by
  unfold degree at *;
  -- Since the set of S where fourier_coeff f S is non-zero is finite, it must have a maximum element in terms of cardinality.
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin n), fourier_coeff f S ≠ 0 ∧ ∀ T : Finset (Fin n), fourier_coeff f T ≠ 0 → T.card ≤ S.card := by
    have h_finite : Set.Finite {S : Finset (Fin n) | fourier_coeff f S ≠ 0} := by
      exact Set.toFinite _;
    apply_rules [ Set.exists_max_image ];
    contrapose! h_finite; aesop;
  refine' ⟨ _, rfl, S, _, hS.1 ⟩;
  refine' le_antisymm _ _;
  · exact Finset.le_sup ( f := Finset.card ) ( by aesop );
  · aesop;
```

This is DEG_WITNESS made formal: a real S with maximal size and nonzero
coefficient.

## Where DEG_WITNESS sits in the proof DAG

From `history/breakdown.md`:

**What DEG_WITNESS represents**
- One existence statement: there is a set S with |S| = degree(f) and
  f_hat(S) != 0.

**What DEG_WITNESS depends on**
- **DEG0**: the definition of degree as a maximum over Fourier support.

**What depends on DEG_WITNESS**
- **EXIST_TOP** (restriction existence): to find a restriction whose *top*
  Fourier coefficient is nonzero, you must first choose the right S.
- **REDUCE** (general degree to full degree): the reduction step starts by
  picking this witness set S.

## How it connects to neighboring concepts

### Connection to DEG0 (definition of degree)
DEG0 defines degree as a max over |S| where f_hat(S) != 0. DEG_WITNESS is the
statement that the max is achieved. Because there are only finitely many S,
this is always true, but you need to say it explicitly to use it later.

### Connection to FULLCOEF (full-degree witness)
FULLCOEF is the special case when the degree equals n. Then the witness set is
forced to be S = all coordinates, and f_hat(univ) != 0. DEG_WITNESS is the
general version where the witness set could be any subset of size k.

### Connection to RESTRICT0 / EXIST_TOP
Once you have S, you restrict f to those coordinates (freeze the rest). The
Fourier-averaging identity then tells you that if f_hat(S) != 0, some
restriction has nonzero top coefficient. That is the EXIST_TOP step, which
feeds the full-degree theorem.

## A tiny example

Suppose f(x1, x2, x3) behaves like the parity of x1 and x2 (plus lower-order
terms). Then the Fourier coefficient at S = {1,2} is nonzero, and any set of
size 3 has zero coefficient. So:

- degree(f) = 2
- a degree witness is S = {1,2}

DEG_WITNESS is the claim that such an S always exists for whatever degree(f)
turns out to be.

## Self-contained takeaway

DEG_WITNESS is the simple but crucial fact that the degree is attained by a
real Fourier term. It upgrades "degree is a number" into "here is the subset
of coordinates responsible for that degree." This concrete S is what lets the
proof zoom into a lower-dimensional subcube and reduce the general case to the
full-degree case.
