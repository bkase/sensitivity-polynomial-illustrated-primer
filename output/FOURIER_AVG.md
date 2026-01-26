# FOURIER_AVG: Fourier averaging over restrictions

## Intuition and motivation
The reduction step in this proof needs a very specific move: if a Fourier coefficient f_hat(S) is nonzero, we want to *find a restriction* of f to the coordinates in S whose top Fourier coefficient is also nonzero. That lets us turn a general-degree function into a full-degree function on a smaller cube.

But how do we guarantee such a restriction exists? FOURIER_AVG is the averaging identity that makes it unavoidable: the average of the top Fourier coefficients of all restrictions equals f_hat(S). If the average is nonzero, at least one term must be nonzero. This is exactly what the next atom **EXIST_TOP** extracts.

So FOURIER_AVG is the bridge between "global Fourier information" and "a concrete subcube where that information is visible." Without it, the restriction-based reduction would have no justification.

## Plain-language statement
Pick a set S of coordinates to keep. For each choice of fixed outside values z, form the restriction f|_{S,z} (a function of only the S-bits). Now look at the *top* Fourier coefficient of that restricted function, i.e., the coefficient at the parity of **all** remaining variables.

FOURIER_AVG says:

```
Original coefficient at S = average over all restrictions of (top coefficient of that restriction)
```

In symbols (ASCII-friendly):

```
f_hat(S) = E_z [ (f|_{S,z})_hat(univ) ]
```

Here `univ` means "all coordinates" *in the restricted domain*, so it is the parity on the remaining |S| variables.

## Why this identity is true (intuition + derivation)
Start from the definition of a Fourier coefficient:

```
f_hat(S) = E_x [ f(x) * chi_S(x) ]
```

Now split each input x into two parts:
- y = the bits on S
- z = the bits outside S

Every x can be written uniquely as (y, z). So the expectation can be rewritten as a two-stage average:

```
f_hat(S) = E_z E_y [ f(y, z) * chi_S(y, z) ]
```

Key observation: chi_S only depends on the bits in S, so:

```
chi_S(y, z) = chi_univ(y)
```

Thus the inner average over y is exactly the top Fourier coefficient of the restricted function f|_{S,z}:

```
E_y [ f(y, z) * chi_univ(y) ] = (f|_{S,z})_hat(univ)
```

Putting it together:

```
f_hat(S) = E_z [ (f|_{S,z})_hat(univ) ]
```

So the identity is really just "rearrange the sum" plus "parity on S ignores outside bits." The Lean proof is long because it handles the indexing and Finset bookkeeping, but the mathematical idea is this simple.

## How it appears in the Lean code
The lemma is stated explicitly in `sensitivity.lean`:

```lean
lemma fourier_coeff_restriction_avg {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) :
  fourier_coeff f S = (Finset.sum Finset.univ (fun z => fourier_coeff (restriction f S z) Finset.univ)) / 2^n := by
    unfold fourier_coeff;
    -- Let's simplify the expression using the definition of `restriction`.
    have h_restrict : ∀ z : Fin n → Bool, (∑ x : Fin (Fintype.card {x : Fin n // x ∈ S}) → Bool, (if (restriction f S z x) then 1 else 0) * chi Finset.univ x) = (∑ x : Fin n → Bool, (if f x then 1 else 0) * (chi S x) * (if ∀ i ∈ Sᶜ, x i = z i then 1 else 0)) := by
      intro z;
      have h_restrict : Finset.sum (Finset.univ.image (fun y : Fin (Fintype.card {x : Fin n // x ∈ S}) → Bool => fun i => if h : i ∈ S then y (Fintype.equivFin {x : Fin n // x ∈ S} ⟨i, h⟩) else z i)) (fun x => (if f x then 1 else 0) * (chi S x)) = Finset.sum (Finset.univ : Finset (Fin (Fintype.card {x : Fin n // x ∈ S}) → Bool)) (fun y => (if (restriction f S z y) then 1 else 0) * (chi Finset.univ y)) := by
        rw [ Finset.sum_image ];
        · refine' Finset.sum_congr rfl fun y hy => _;
          unfold chi restriction; simp +decide ;
          rw [ Finset.card_filter ];
          rw [ ← Finset.sum_attach ];
          rw [ Finset.card_filter ];
          rw [ ← Equiv.sum_comp ( Fintype.equivFin { x // x ∈ S } ) ] ; aesop;
        · intro y hy y' hy' h_eq;
          ext i; replace h_eq := congr_fun h_eq ( Fintype.equivFin { x // x ∈ S } |>.symm i ) ; aesop;
      rw [ ← h_restrict, Finset.sum_image ];
      · rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun y : Fin ( Fintype.card { x // x ∈ S } ) → Bool => fun i => if h : i ∈ S then y ( Fintype.equivFin { x // x ∈ S } ⟨ i, h ⟩ ) else z i ) Finset.univ ) ) ];
        · rw [ Finset.sum_image ];
          · exact Finset.sum_congr rfl fun x hx => by aesop;
          · intro y₁ hy₁ y₂ hy₂ h_eq; ext i; replace h_eq := congr_fun h_eq ( Fintype.equivFin { x // x ∈ S } |>.symm i ) ; aesop;
        · simp +zetaDelta at *;
          intro x hx₁ hx₂ hx₃; specialize hx₁ ( fun i => x ( Fintype.equivFin { x // x ∈ S } |>.symm i ) ) ; simp_all +decide [ funext_iff ] ;
      · intro y₁ hy₁ y₂ hy₂ h_eq; ext i; replace h_eq := congr_fun h_eq ( Fintype.equivFin { x // x ∈ S } |>.symm i ) ; aesop;
    have h_restrict : ∀ x : Fin n → Bool, ∑ z : Fin n → Bool, (if ∀ i ∈ Sᶜ, x i = z i then 1 else 0) = 2 ^ (Finset.card S) := by
      intros x
      have h_restrict : Finset.card (Finset.filter (fun z : Fin n → Bool => ∀ i ∈ Sᶜ, x i = z i) Finset.univ) = 2 ^ (Finset.card S) := by
        have h_restrict : Finset.card (Finset.image (fun z : Fin n → Bool => fun i : S => z i) (Finset.filter (fun z : Fin n → Bool => ∀ i ∈ Sᶜ, x i = z i) Finset.univ)) = 2 ^ (Finset.card S) := by
          rw [ show ( Finset.image ( fun z : Fin n → Bool => fun i : S => z i ) { z : Fin n → Bool | ∀ i ∈ Sᶜ, x i = z i } ) = Finset.univ from ?_ ];
          · simp +decide [ Finset.card_univ ];
          · ext z; simp [Finset.mem_image];
            use fun i => if hi : i ∈ S then z ⟨ i, hi ⟩ else x i; aesop;
        rw [ ← h_restrict, Finset.card_image_of_injOn ];
        intros z hz z' hz' h_eq;
        simp +zetaDelta at *;
        ext i; by_cases hi : i ∈ S <;> simp_all +decide [ funext_iff ] ;
      aesop;
    have h_restrict : ∑ z : Fin n → Bool, ∑ x : Fin n → Bool, (if f x then 1 else 0) * (chi S x) * (if ∀ i ∈ Sᶜ, x i = z i then 1 else 0) = ∑ x : Fin n → Bool, (if f x then 1 else 0) * (chi S x) * 2 ^ (Finset.card S) := by
      rw [ Finset.sum_comm ];
      simp +decide only [← Finset.mul_sum _ _ _, ← Finset.sum_mul];
      rw [ Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => by aesop;
    have h_restrict : ∑ z : Fin n → Bool, ∑ x : Fin (Fintype.card {x : Fin n // x ∈ S}) → Bool, (if (restriction f S z x) then 1 else 0) * chi Finset.univ x = ∑ x : Fin n → Bool, (if f x then 1 else 0) * (chi S x) * 2 ^ (Finset.card S) := by
      rw [ ← h_restrict, Finset.sum_congr rfl fun _ _ => ‹∀ z : Fin n → Bool, ∑ x : Fin ( Fintype.card { x // x ∈ S } ) → Bool, ( if restriction f S z x = true then 1 else 0 ) * chi Finset.univ x = ∑ x : Fin n → Bool, ( if f x = true then 1 else 0 ) * chi S x * if ∀ i ∈ Sᶜ, x i = z i then 1 else 0› _ ];
    rw [ ← Finset.sum_div _ _ _ ];
    rw [ h_restrict, ← Finset.sum_mul _ _ _ ];
    norm_num [ Fintype.card_subtype ]
```

What to notice:
- `fourier_coeff` is defined as an average over all inputs.
- `restriction f S z` is the restricted function on the S-coordinates.
- `Finset.univ` is the set of all assignments (so the sum is an average).
- The division by `2^n` turns the full sum over all z into the expectation E_z.

Lean sums over all z in {0,1}^n, even though the restriction only depends on z outside S. That means each distinct restriction is repeated 2^{|S|} times, and the factors cancel in the average. The equality still holds.

## Dependencies and what depends on FOURIER_AVG (from breakdown.md)

**What FOURIER_AVG represents**
- The averaging identity linking f_hat(S) to top coefficients of restrictions.

**What FOURIER_AVG depends on**
- **CHI0**: parity characters chi_S.
- **FOURIER0**: definition of Fourier coefficients as averages.
- **RESTRICT0**: restriction to a subcube by fixing outside bits.

**What depends on FOURIER_AVG**
- **EXIST_TOP**: if the average is nonzero, some restriction has nonzero top coefficient.
- This then feeds **DEG_FROM_TOP** and the full reduction chain (**REDUCE**).

## Connection to neighboring concepts in the proof
Here is the local pipeline around FOURIER_AVG:

1) **DEG_WITNESS** gives S with |S| = degree(f) and f_hat(S) != 0.
2) **FOURIER_AVG** rewrites f_hat(S) as an average over restrictions.
3) **EXIST_TOP** concludes there exists z with (f|_{S,z})_hat(univ) != 0.
4) **DEG_FROM_TOP** says that restriction has full degree |S|.
5) **FULLCASE** applies to that restricted function.
6) **SENS_MONO** lifts the sensitivity bound back to the original f.

So FOURIER_AVG is the key identity that makes the restriction trick mathematically valid.

## Small example (n = 2)
Let f(x1, x2) = x1 (as a 0/1-valued function). Take S = {1}.

Compute the original coefficient:
- chi_S(x) = +1 if x1 = 0, and -1 if x1 = 1.
- f(x) is 1 only when x1 = 1.

So:

```
f_hat({1}) = (1/4) * [0 + 0 + (-1) + (-1)] = -1/2
```

Now restrict to S by fixing x2:
- If z2 = 0, f|_{S,z}(y) = y
- If z2 = 1, f|_{S,z}(y) = y

For the 1-bit function g(y) = y:

```
g_hat(univ) = (1/2) * [0*(+1) + 1*(-1)] = -1/2
```

Average over both z2 values: still -1/2, matching f_hat({1}).

## Takeaway
FOURIER_AVG is the averaging identity that lets the proof move from a nonzero Fourier coefficient at S to a concrete restriction with a nonzero top coefficient. Conceptually, it says:

"If a parity pattern is present globally, then on average it is present in the slices where you freeze the other variables."

That single fact is the hinge of the restriction-based reduction step in the Sensitivity Conjecture proof.
