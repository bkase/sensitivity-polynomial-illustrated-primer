# RESTRICT0: Restriction (freeze outside S)

## Intuition and motivation
The proof often needs to reduce a big Boolean function on n variables to a smaller one on fewer variables, without losing the key property we care about (degree and sensitivity). Restriction is the standard way to do that: you "freeze" some input bits to fixed values and only allow the remaining bits to vary. This turns the original function into a new function on a lower-dimensional cube, i.e., a subcube (a face) of the original hypercube.

Think of f as a control panel with n switches. A restriction is: "lock some switches in place, and only play with the rest." The resulting behavior is still a Boolean function, just on fewer switches. This is crucial for the reduction step of the proof: we want to take a function with degree d and restrict it to a d-dimensional subcube where the restricted function has full degree.

## Plain-language definition
Let f be a Boolean function on n bits. Choose:
- a set S of coordinates you will *keep* (the "free" bits),
- and a fixed assignment z to all n coordinates (used only outside S).

The restriction f|_{S,z} is the new function that:
- takes only |S| input bits (one bit for each coordinate in S),
- plugs those bits into the corresponding positions of f,
- and fills the remaining positions (outside S) with the fixed values from z.

In symbols:

```
Given S subset [n] and z in {0,1}^n,
define f|_{S,z}(y) = f(x), where
  x_i = y_i   if i in S
  x_i = z_i   if i not in S
```

So f|_{S,z} is just f restricted to the subcube where all coordinates outside S are fixed to match z.

## Visual/analogy: faces of a cube
In a 3D cube, fixing one coordinate gives you a square face. Fixing two coordinates gives you an edge. Fixing three gives you a single vertex. In higher dimensions, the same idea holds: a restriction chooses a lower-dimensional face (a subcube) of the n-dimensional hypercube.

This is why the lecture notes say "restrict to the subcube Q_T": you pick a subset of coordinates T and look only at points that agree with some fixed outside assignment.

## How RESTRICT0 appears in the Lean code
Here is the definition from `sensitivity.lean`:

```lean
def restriction {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (z : Fin n → Bool) : (Fin (Fintype.card {x // x ∈ S}) → Bool) → Bool :=
  fun y =>
    let x : Fin n → Bool := fun i =>
      if h : i ∈ S then
        y (Fintype.equivFin {j // j ∈ S} ⟨i, h⟩)
      else
        z i
    f x
```

How to read this:
- `y` is an input on the smaller cube (one bit per element of S).
- The code builds a full n-bit input `x` by:
  - using `y` on positions i in S,
  - using the fixed assignment `z` on positions outside S.
- Then it applies `f` to that reconstructed `x`.

The `Fintype.equivFin` part is just Lean bookkeeping: it converts "the i-th element of S" into a number from 0 to |S|-1 so `y` can be indexed.

## Dependencies and what depends on RESTRICT0 (from breakdown.md)

**What RESTRICT0 represents**
- The construction "freeze outside S using z," producing a smaller-dimensional Boolean function.

**What RESTRICT0 depends on**
- **BC0**: the universe of inputs as functions `Fin n -> Bool`, so we can talk about coordinates, subsets of coordinates, and fixed assignments.

**What depends on RESTRICT0**
- **SENS_MONO**: restriction cannot increase sensitivity; you remove edges, so local counts can only go down.
- **FOURIER_AVG**: the Fourier coefficient f^(S) equals the average of the top Fourier coefficients of the restricted functions.

Those two facts are the core of the reduction step (**REDUCE**), which turns "degree d" into "full degree on a d-dimensional subcube."

## How it connects to neighboring concepts in the proof
Restriction is the gateway from general degree to full degree:
1. **DEG_WITNESS** gives a set S with |S| = degree(f) and f^(S) != 0.
2. **FOURIER_AVG** says f^(S) is the average of the top coefficients of f|_{S,z} over all z.
3. **EXIST_TOP** then guarantees there is some z where the top coefficient of f|_{S,z} is nonzero.
4. **DEG_FROM_TOP** upgrades that to: f|_{S,z} has full degree |S|.
5. **FULLCASE** applies to that restricted function.
6. **SENS_MONO** lifts the sensitivity bound back to the original f.

So RESTRICT0 is the basic construction that makes this reduction pipeline possible.

## Small concrete example
Let f(x1, x2, x3) = x1 XOR x2 (ignoring x3).
Take S = {1, 3} and let z fix x2 = 0.
Then f|_{S,z} is a function of two bits (x1, x3):

```
f|_{S,z}(y1, y3) = f(y1, 0, y3) = y1 XOR 0 = y1
```

So restriction removed x2 entirely (because we froze it), and the new function depends only on the remaining free coordinates in S.

## Takeaway
RESTRICT0 is the formal "freeze some variables" operation. It produces a smaller Boolean function by fixing coordinates outside a chosen set S to a fixed assignment z. This is the key tool that lets the proof reduce the general-degree case to the full-degree case while controlling sensitivity and Fourier coefficients.
