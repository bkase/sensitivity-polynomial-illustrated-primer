# SENS_MONO: Sensitivity is monotone under restriction

## Intuition and motivation
The proof repeatedly "zooms in" on a subcube by freezing some variables, because that is how we turn a general-degree function into a full-degree one. But once we do that, we need a safe way to carry any lower bound on sensitivity back to the original function. SENS_MONO is exactly that safety valve:

**If you lock some switches in place, you cannot make the system more fragile.**

So if the restricted function is already highly sensitive, the original function must be at least that sensitive. This is the key step that lets the reduction (REDUCE) finish.

Analogy: imagine a city map where intersections are inputs and roads are one-bit flips. Sensitivity at a point is "how many roads out of this intersection change the output." If you close some streets and only look at a smaller neighborhood (a restriction), you cannot *increase* the maximum number of roads leaving any intersection. You only remove roads.

## Plain-language statement
Let f be a Boolean function on n bits. Pick a subset S of bits to keep free, and fix all other bits to a pattern z. This gives a restricted function f|_{S,z} on |S| bits. Then:

```
s(f|_{S,z}) <= s(f)
```

In words: the sensitivity of a restriction is at most the sensitivity of the original function.

This relies on the definitions:
- **SEN0**: sensitivity is the maximum number of one-bit neighbors that flip f.
- **RESTRICT0**: restriction means "freeze outside S and keep only the bits in S."

## Why this is true (informal proof sketch)
Think in the hypercube graph:
- Each vertex is an input x in {0,1}^n.
- An edge connects x to y if they differ in exactly one bit.

A restriction f|_{S,z} lives on a *subcube* (a face) where all coordinates outside S are fixed. The edges of this subcube are a subset of the original cube's edges.

Now take any input y in the restricted cube. Map it back to the corresponding full input x (fill in the frozen bits with z). Every neighbor y' of y in the restricted cube corresponds to a neighbor x' of x in the full cube. If f|_{S,z} changes across y--y', then f changes across x--x'. Therefore:

```
local_sensitivity(f|_{S,z}, y) <= local_sensitivity(f, x)
```

Taking the maximum over all y on the restricted cube gives:

```
s(f|_{S,z}) <= s(f)
```

No new edges are created by restriction, so the maximum "edge-boundary degree" cannot go up.

## How it appears in the Lean code
The restriction and the monotonicity lemma are defined in `sensitivity.lean`:

```lean
def restriction {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (z : Fin n → Bool) : (Fin (Fintype.card {x // x ∈ S}) → Bool) → Bool :=
  fun y =>
    let x : Fin n → Bool := fun i =>
      if h : i ∈ S then
        y (Fintype.equivFin {j // j ∈ S} ⟨i, h⟩)
      else
        z i
    f x

lemma sensitivity_restriction_le {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (z : Fin n → Bool) :
  sensitivity (restriction f S z) ≤ sensitivity f := by
    unfold sensitivity;
    simp +decide only [Finset.sup_le_iff];
    intro x;
    simp +decide [ restriction ];
    refine' le_trans _ ( Finset.le_sup <| Finset.mem_univ <| fun i => if h : i ∈ S then x ( Fintype.equivFin _ ⟨ i, h ⟩ ) else z i );
    refine' le_trans _ ( Finset.card_le_card _ );
    rotate_left;
    exact Finset.image ( fun y : Fin ( Fintype.card { x // x ∈ S }) → Bool => fun i => if h : i ∈ S then y ( Fintype.equivFin _ ⟨ i, h ⟩ ) else z i ) ( Finset.filter ( fun y => Finset.card ( Finset.filter ( fun i => ¬x i = y i ) Finset.univ ) = 1 ∧ ¬f ( fun i => if h : i ∈ S then x ( Fintype.equivFin _ ⟨ i, h ⟩ ) else z i ) = f ( fun i => if h : i ∈ S then y ( Fintype.equivFin _ ⟨ i, h ⟩ ) else z i ) ) ( Finset.univ : Finset ( Fin ( Fintype.card { x // x ∈ S }) → Bool ) ) );
    · simp +decide [ Finset.subset_iff ];
      rintro _ y hy₁ hy₂ rfl; simp_all +decide [ Finset.card_eq_one ] ;
      obtain ⟨ a, ha ⟩ := hy₁; use ( Fintype.equivFin { x // x ∈ S } ).symm a; ext i; by_cases hi : i ∈ S <;> simp_all +decide [ Finset.ext_iff ] ;
      · aesop;
      · intro H; have := ha a; simp_all +decide [ Fin.ext_iff ] ;
    · rw [ Finset.card_image_of_injective ];
      intro y₁ y₂ hy; ext i; replace hy := congr_fun hy ( Fintype.equivFin { x // x ∈ S } |>.symm i ) ; aesop;
```

The proof in Lean is technical (it unfolds definitions and compares two Finset counts), but the idea is exactly the graph argument above: every sensitive neighbor in the restriction corresponds to a sensitive neighbor in the original function.

This lemma is used in the final reduction:

```lean
    -- By `sensitivity_restriction_le`, sensitivity f ≥ sensitivity g.
    have h_sens_f : (sensitivity f : ℝ) ≥ (sensitivity (restriction f S z) : ℝ) := by
      exact_mod_cast sensitivity_restriction_le f S z;
```

## Dependencies and what depends on SENS_MONO (from breakdown.md)

**What SENS_MONO represents**
- The monotonicity fact: "restriction cannot increase sensitivity."

**What SENS_MONO depends on**
- **SEN0**: the definition of sensitivity.
- **RESTRICT0**: the definition of restriction.

**What depends on SENS_MONO**
- **REDUCE**: the general-degree reduction uses SENS_MONO to lift the sensitivity lower bound from the restricted function back to the original f.

## How it connects to neighboring concepts in the proof
SENS_MONO is the last step of the restriction pipeline:

1. **DEG_WITNESS**: pick a set S that witnesses the degree (f_hat(S) != 0).
2. **FOURIER_AVG** + **EXIST_TOP**: find a restriction f|_{S,z} with nonzero top coefficient.
3. **DEG_FROM_TOP**: conclude the restriction has full degree |S|.
4. **FULLCASE**: apply the full-degree sensitivity lower bound to the restriction.
5. **SENS_MONO**: lift that lower bound back to the original function.

Without SENS_MONO, the chain would stop at step 4 and never return to the original f.

## Small concrete example
Let f(x1, x2, x3) = x1 XOR x2.
- For any input, flipping x1 or x2 changes f, but flipping x3 does not.
- So s(f) = 2.

Restrict by fixing x2 = 0 and keeping S = {x1, x3}. Then:

```
g(x1, x3) = f(x1, 0, x3) = x1
```

Now g only changes when x1 flips, so s(g) = 1. This matches SENS_MONO:

```
s(g) = 1 <= 2 = s(f)
```

## Takeaway
SENS_MONO says: *restricting a Boolean function cannot make it more sensitive*. It formalizes the intuition that when you freeze variables, you only remove possible one-bit changes. This monotonicity is the bridge that lets the proof focus on a high-degree restriction and then carry the sensitivity bound back to the original function.
