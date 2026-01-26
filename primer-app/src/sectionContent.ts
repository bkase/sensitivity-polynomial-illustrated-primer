// Auto-generated MDX content for each section
// Each section contains the explanation for that part of the Lean proof

export const sectionContent: Record<number, string> = {};

sectionContent[1] = `# Generalizing proofs in Lean: \`Harmonic.GeneralizeProofs\`

This section defines a customized version of Mathlib’s \`generalize_proofs\` tactic. The goal of the tactic is to **remove proof-term dependencies from definitional equality** by turning those proofs into explicit arguments. In large formalizations (like the Sensitivity Conjecture), this prevents Lean from getting stuck on “the same proposition, but different proof objects,” and makes rewriting and definitional reduction far more robust.

Below is a guided tour of what the code does and why it matters.

## Big picture: what \`generalize_proofs\` does

Lean’s definitional equality treats proofs as data. When you build terms that depend on a proof (for example, a dependent \`Subtype\`, \`Finset\` membership proof, or a lemma packaged into a structure), the *exact proof term* can affect whether two expressions are definitionally equal. Two mathematically identical proofs can still be different terms, and that can block rewriting or \`simp\` from closing a goal.

\`generalize_proofs\` fixes this by:

1. Scanning a term (the goal or selected hypotheses).
2. Finding proof terms that occur inside it.
3. Abstracting those proofs into fresh variables.
4. Replacing the original proof terms with those variables.

After the tactic, your goal is definitionally equal to a version that no longer hardcodes those proof objects. This makes subsequent transformations and rewrites *proof-irrelevant in practice*, even when Lean’s kernel still distinguishes proof terms.

## Walkthrough of the implementation

### 1. \`mkLambdaFVarsUsedOnly'\`
\`\`\`lean
-- Like Mathlib’s helper, but keeps all fvars (usedOnly := false).
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr)
\`\`\`
This function wraps an expression in lambdas over a list of free variables, but **does not drop “unused” binders** (\`usedOnly := false\`). This is crucial when abstracting proofs: a proof might be needed for type-checking even if it is not syntactically referenced after reduction. Keeping all binders avoids accidentally losing dependencies.

### 2. \`abstractProofs'\`
\`\`\`lean
partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr
\`\`\`
This is the main traversal. It walks the expression tree and, whenever it encounters a proof term, it:

- Beta-reduces and normalizes the proof.
- Lambda-abstracts over the current local proof variables.
- Stores the generalized proof term in an internal cache (\`MAbs.insertProof\`).
- Replaces the original proof occurrence with an application of the generalized proof to the local proof variables.

The result is an expression where each proof is “lifted out” and can be introduced as a fresh hypothesis later.

Two key details:

- **\`config.maxDepth\`**: limits recursion for performance; beyond that, it leaves the term as-is.
- **\`config.abstract\`**: if false and a proof depends on locals, it won’t be abstracted. This preserves behavior in sensitive contexts.

### 3. \`withGeneralizedProofs'\`
\`\`\`lean
partial def withGeneralizedProofs' {α} ... (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) : MGen α
\`\`\`
This wraps \`abstractProofs'\` and **materializes** the generalizations as new local hypotheses:

- It runs \`abstractProofs'\` to collect the proof terms that should be abstracted.
- For each collected proof type, it creates a new local hypothesis.
- It replaces proof occurrences in the expression with those new fvars.

The callback \`k\` then receives:

- \`fvars\`: the new proof variables introduced,
- \`pfs\`: the generalized proof terms (as lambda-expressions),
- \`e'\`: the updated expression with abstracted proofs.

### 4. \`generalizeProofsCore'\`
\`\`\`lean
partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool)
\`\`\`
This is the core tactic logic. It:

1. Reverts the selected hypotheses (or all hypotheses if \`location\` is \`*\`).
2. Re-introduces them one-by-one.
3. While re-introducing, it runs \`withGeneralizedProofs'\` on each type to generalize proofs inside the binder type.
4. Optionally generalizes proofs in the **target** (if \`target = true\`).

There’s also a specialized path for let-bound proofs and proof hypotheses already in the context (\`propToFVar\`) to reuse existing proof variables rather than introduce duplicates.

### 5. \`generalizeProofs'\` and the elaborator
\`\`\`lean
elab (name := generalizeProofsElab'') "generalize_proofs" ...
\`\`\`
This installs the tactic so it behaves like Mathlib’s \`generalize_proofs\`, but uses the modified helpers above. You can call it as:

- \`generalize_proofs\` — generalize proofs in all hypotheses and the target.
- \`generalize_proofs at h1 h2\` — only in specific hypotheses.
- \`generalize_proofs at *\` — all hypotheses.

The optional binder identifiers let you name the newly introduced proof variables.

## Why this matters for the Sensitivity Conjecture proof

The Sensitivity Conjecture formalization involves deep chains of dependent definitions—finite sets, subtypes, and structures whose fields contain proof objects (e.g., membership proofs, bound proofs, and proof-carrying indices). In such environments:

- Many expressions are **definitionally equal only if their internal proof terms match exactly**.
- Rewriting and simplification can get stuck because proof terms differ even though the propositions are equivalent.
- Tactics that rely on definitional equality (like \`simp\`, \`cases\`, \`rfl\`, or automation) can fail unexpectedly or create fragile proof scripts.

\`Harmonic.GeneralizeProofs.generalize_proofs\` eliminates these issues by **making those proof terms explicit parameters**. Once a proof is an argument rather than hidden inside a definition, Lean stops requiring exact proof-term equality to reduce or rewrite. In practice, this makes the large, compositional steps in the Sensitivity Conjecture proof *stable and predictable*.

### Intuition in one sentence
You can think of \`generalize_proofs\` as “proof-irrelevance on demand”: it rewrites a goal so that the proof objects stop mattering for definitional equality, which is exactly what you want in a long, dependent proof like the Sensitivity Conjecture.

## Minimal example (conceptual)

Suppose you have a term that depends on two different proofs of the same fact. Those proofs are not definitionally equal, so rewriting fails. After \`generalize_proofs\`, both are replaced by a fresh variable, and definitional equality no longer cares which proof was used.

This is precisely the kind of technical friction the Sensitivity Conjecture proof would otherwise face repeatedly.
`;

sectionContent[2] = `# Section 2: Sensitivity in Lean

This section defines the *sensitivity* of a Boolean function — the central concept in the Sensitivity Conjecture.

## What sensitivity measures

For a Boolean function \\(f : \\{0,1\\}^n \\to \\{0,1\\}\\), the **sensitivity** of \`f\` is the maximum, over all inputs \`x\`, of how many single-bit flips change the output. Informally:

- Fix an input \`x\`.
- Flip exactly one coordinate to get a neighbor \`y\`.
- Count how many such neighbors change \`f\`'s value.
- Sensitivity is the maximum of that count over all \`x\`.

So sensitivity measures how locally "fragile" the function is: if many one-bit changes flip the output, \`f\` is highly sensitive at that input.

## The Lean definition

The code in this section is:

\`\`\`lean
def sensitivity {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.sup Finset.univ (fun x =>
    Finset.card
      (Finset.filter
        (fun y =>
          (Finset.card (Finset.filter (fun i => x i ≠ y i) Finset.univ) = 1)
          ∧ f x ≠ f y)
        Finset.univ))
\`\`\`

Let's unpack this in pieces.

### Term-level definition (no tactics)

This snippet is written entirely in **term mode** (a direct expression), not in tactic mode. There are **no tactics** here — no \`by\`, \`simp\`, \`linarith\`, etc. Everything is a nested expression that Lean can typecheck without any proof scripting.

### Types and inputs

- \`n : ℕ\` is the input size.
- An input vector \`x\` is represented as a function \`Fin n → Bool\`, i.e., a Boolean value for each index \`0, 1, ..., n-1\`.
- The Boolean function is \`f : (Fin n → Bool) → Bool\`.

Additional Lean details:

- \`def sensitivity {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := ...\`
  - \`def\` introduces a new constant with a definition.
  - \`{n : ℕ}\` uses **implicit binder** syntax: the curly braces mean Lean will usually infer \`n\`.
  - \`(f : (Fin n → Bool) → Bool)\` is an **explicit binder**: \`f\` must be supplied.
  - \`: ℕ\` states the **result type** of the definition.
  - \`:=\` separates the name/signature from the defining expression.
  - Parentheses are used for grouping types and binders; arrows \`→\` associate to the right.

**Correspondence with standard notation**: In the mathematical literature, inputs are elements of \`{0,1}^n\`. In Lean, we use \`Fin n → Bool\` with the convention:
- \`false\` corresponds to \`0\`
- \`true\` corresponds to \`1\`

So a Boolean vector like \`(0, 1, 1, 0)\` becomes the function \`fun i => if i = 1 ∨ i = 2 then true else false\`.

### Finsets and \`Finset.univ\`

Lean uses finite sets (\`Finset\`) to quantify over all elements of a finite type. Here:

- \`Finset.univ\` over \`Fin n → Bool\` is the set of all Boolean vectors of length \`n\`.
- \`Finset.univ\` over \`Fin n\` is the set of all indices \`0..n-1\`.
- \`Finset\` is a data type for finite sets with decidable equality; it carries a list-like representation plus proofs that duplicates are removed.

**Why this works**: Lean knows that \`Fin n → Bool\` is a finite type via the \`Fintype\` instance for function types. Specifically, \`Fintype.card (Fin n → Bool) = 2^n\` because there are 2 choices (true/false) for each of the \`n\` positions. This instance allows \`Finset.univ\` to enumerate all \`2^n\` Boolean vectors.

### Counting Hamming distance 1

Inside the definition, this fragment:

\`\`\`lean
Finset.card (Finset.filter (fun i => x i ≠ y i) Finset.univ)
\`\`\`

counts the number of indices \`i\` where \`x i\` differs from \`y i\`. This is the Hamming distance between \`x\` and \`y\`.

Lean syntax details here:

- \`fun i => ...\` is a **lambda expression** (anonymous function). The \`=>\` introduces the body.
- \`x i\` is **function application**: \`x\` is a function \`Fin n → Bool\`, so \`x i\` is a \`Bool\`.
- \`≠\` is notation for \`Not ( = )\`, producing a **proposition** (\`Prop\`). For \`Bool\`, Lean uses the \`DecidableEq\` instance to decide equality.
- \`Finset.filter\` expects a **decidable predicate** \`α → Prop\`; the system infers decidability for \`x i ≠ y i\`.
- \`Finset.card\` returns a **natural number** (\`ℕ\`) counting elements of the filtered finset.

The condition

\`\`\`lean
(... = 1)
\`\`\`

forces \`y\` to differ from \`x\` in exactly one coordinate.

### Counting sensitive neighbors

The inner filter is:

\`\`\`lean
Finset.filter (fun y => (distance = 1) ∧ f x ≠ f y) Finset.univ
\`\`\`

So for a fixed \`x\`, it keeps all \`y\` with Hamming distance 1 from \`x\` and where \`f\` flips value. Then:

\`\`\`lean
Finset.card (...)
\`\`\`

counts how many such \`y\` exist. This is the **sensitivity of \`f\` at \`x\`**.

Lean syntax details in this predicate:

- \`∧\` is logical **conjunction** (\`And\`) in \`Prop\`.
- \`f x\` applies the Boolean function to an input, so \`f x : Bool\`.
- \`f x ≠ f y\` is a proposition about Boolean inequality (not a Boolean XOR).
- The whole predicate \`(... = 1) ∧ f x ≠ f y\` lives in \`Prop\` and is used by \`Finset.filter\`.

### Taking the maximum

Finally,

\`\`\`lean
Finset.sup Finset.univ (fun x => ...)
\`\`\`

computes the supremum of that count across all inputs \`x\`. This yields the overall sensitivity of \`f\`.

Lean syntax details here:

- \`Finset.sup\` takes a finset and a function; its second argument is the \`fun x => ...\` lambda.
- The \`x\` bound by \`fun x =>\` is implicitly typed as \`Fin n → Bool\` because \`Finset.univ\` ranges over that type.
- Lean uses **typeclass inference** to pick the \`sup\` operation for \`ℕ\` and the bottom element \`⊥\`.

**Technical note on \`Finset.sup\`**: This is the lattice supremum operation. For natural numbers (\`ℕ\`), the lattice supremum is simply the maximum. The function \`Finset.sup\` requires a \`SemilatticeSup\` instance with a bottom element \`⊥\`; for \`ℕ\`, this bottom is \`0\`. If the set is empty, \`Finset.sup\` returns \`⊥ = 0\`. For nonempty sets, you could equivalently use \`Finset.sup'\` which doesn't need the bottom element but requires a nonemptiness proof.

## Worked example: the OR function

Let \`n = 3\` and define \`f\` to be the OR function:

\`\`\`lean
def or3 : (Fin 3 → Bool) → Bool := fun x => x 0 || x 1 || x 2
\`\`\`

In standard notation, \`or3(x₀, x₁, x₂) = x₀ ∨ x₁ ∨ x₂\`, which is \`true\` if any bit is \`true\`.

**Analyzing sensitivity at each input:**

- \`x = (false, false, false)\` (the all-zeros input):
  - Neighbors are \`(true, false, false)\`, \`(false, true, false)\`, \`(false, false, true)\`
  - All three neighbors have \`or3 = true\`, while \`or3 x = false\`
  - So sensitivity at this input is **3**

- \`x = (true, true, true)\` (the all-ones input):
  - Neighbors are \`(false, true, true)\`, \`(true, false, true)\`, \`(true, true, false)\`
  - All three neighbors still have \`or3 = true\`, same as \`or3 x = true\`
  - So sensitivity at this input is **0**

- \`x = (true, false, false)\`:
  - Neighbors: \`(false, false, false)\` has \`or3 = false\` ≠ \`or3 x = true\` ✓
  - Neighbors: \`(true, true, false)\` and \`(true, false, true)\` have \`or3 = true\` = \`or3 x\`
  - So sensitivity at this input is **1**

The maximum over all 8 inputs is **3**, achieved at the all-zeros input. Thus \`sensitivity or3 = 3\`.

In Lean, the definition enumerates all \`x : Fin 3 → Bool\` (8 inputs), counts sensitive neighbors for each, and takes the maximum via \`Finset.sup\`.

## Lean syntax cheat sheet

- \`def name := ...\` introduces a definition.
- \`{n : ℕ}\` is an implicit argument (Lean can usually infer it).
- \`(Fin n → Bool)\` is the type of Boolean vectors of length \`n\`.
- \`fun x => ...\` is an anonymous function; \`=>\` separates its body.
- \`x i\` is function application; there are no commas for arguments.
- \`:=\` introduces a definition body.
- \`=\` is propositional equality; \`≠\` is \`Not ( = )\`.
- \`∧\` is logical conjunction in \`Prop\`.
- \`Finset.filter\` keeps elements that satisfy a predicate.
- \`Finset.card\` counts elements in a finite set.
- \`Finset.sup\` takes the maximum of a function over a finite set.

## Formal mathematical definition

For completeness, here is the standard mathematical definition that the Lean code encodes:

**Definition**: The **sensitivity at input \\(x\\)** is:
\\[
s(f, x) = |\\{i \\in [n] : f(x) \\neq f(x^{\\oplus i})\\}|
\\]
where \\(x^{\\oplus i}\\) denotes \\(x\\) with the \\(i\\)-th bit flipped.

**Definition**: The **sensitivity of \\(f\\)** is:
\\[
s(f) = \\max_{x \\in \\{0,1\\}^n} s(f, x)
\\]

The Lean definition directly implements this: \`Finset.filter\` computes the set \\(\\{i : f(x) \\neq f(x^{\\oplus i})\\}\\), \`Finset.card\` computes its cardinality, and \`Finset.sup\` computes the maximum.

## Summary

- The definition computes the maximum number of one-bit flips that change \\(f\\).
- It uses \`Finset.univ\` to enumerate all inputs and all indices.
- The Hamming distance test \`= 1\` enforces single-bit flips.
- The final \`Finset.sup\` takes the maximum over all inputs.

This is a direct, faithful Lean translation of the standard mathematical definition of sensitivity.
`;

sectionContent[3] = `# Section 3: The Parity Character χ_S

This section defines the Boolean character \\(\\chi_S(x)\\), a basic building block of Fourier analysis on the Boolean cube \\(\\{0,1\\}^n\\).

## Definition in math form

The Lean code defines:

\`\`\`lean
def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  if (Finset.filter (fun i => x i) S).card % 2 = 0 then 1 else -1
\`\`\`

Lean syntax walkthrough (no tactics are used here; it's a single definition):
- \`def chi ... :=\` introduces a new definition named \`chi\` and gives its body after \`:=\`.
- \`{n : ℕ}\` is an implicit parameter (Lean will usually infer \`n\`), and \`ℕ\` is the natural numbers type.
- \`(S : Finset (Fin n))\` means \`S\` is a finite set of indices; \`Fin n\` is the type of numbers \`0, 1, ..., n-1\`.
- \`(x : Fin n → Bool)\` means \`x\` is a function taking an index \`i : Fin n\` to a Boolean value; \`→\` is the function type arrow.
- \`: ℝ\` is the return type; the output is a real number.
- \`if ... then ... else ...\` is a term-level conditional; Lean uses a decidable test here and returns \`1\` or \`-1\` accordingly.
- \`Finset.filter (fun i => x i) S\` filters \`S\` by the predicate \`fun i => x i\`; \`fun i => ...\` is a lambda (anonymous function).
- \`.card\` is field notation for \`Finset.card\`, giving the number of elements.
- \`% 2\` is modulus on naturals; \`= 0\` checks whether the remainder is zero (even parity).
- \`1\` and \`-1\` are numerals interpreted as reals because the whole expression has type \`ℝ\`.

Translated to math, if we view a Boolean input \\(x : \\{0,1\\}^n\\) and a subset \\(S \\subseteq [n]\\), then

\\[
\\chi_S(x) = (-1)^{|\\{ i \\in S : x_i = 1 \\}|}.
\\]

In words: count how many indices in \\(S\\) have value 1 under \\(x\\). If that count is even, \\(\\chi_S(x) = 1\\); if it is odd, \\(\\chi_S(x) = -1\\).

The code expresses exactly this parity test:
- \`Finset.filter (fun i => x i) S\` is the subset of \\(S\\) where \\(x_i\\) is true.
- \`.card % 2\` takes the parity of that count.
- Even parity gives \`1\`, odd parity gives \`-1\`.

Additional Lean details tied to that line:
- \`x i\` is function application (apply \`x\` to index \`i\`); parentheses are used when chaining applications.
- \`Finset.filter\` expects a Boolean predicate, so \`x i\` is used directly (no \`x i = true\` needed).
- \`card\` returns a natural number, so \`% 2\` computes the remainder mod 2 on \`ℕ\`.
- The equality \`= 0\` is a proposition Lean can decide, which is what powers the \`if\`.

## Why it always returns ±1

Because \\(\\chi_S(x)\\) is defined as a parity test, it has only two possible outcomes:
- If the count of ones in \\(S\\) is even, then \\(\\chi_S(x)=1\\).
- If the count is odd, then \\(\\chi_S(x)=-1\\).

There is no other possibility. Parity only distinguishes even vs. odd, so the output is always \\(+1\\) or \\(-1\\).

Another way to see this is through the exponent form:
\\[
\\chi_S(x) = (-1)^{k}, \\quad k = |\\{ i \\in S : x_i = 1 \\}|.
\\]
When \\(k\\) is even, \\((-1)^k=1\\); when \\(k\\) is odd, \\((-1)^k=-1\\).

## Role in Fourier analysis on the Boolean cube

The characters \\(\\chi_S\\) form the Fourier basis for functions \\(f : \\{0,1\\}^n \\to \\mathbb{R}\\). Concretely:

- The collection \\(\\{\\chi_S : S \\subseteq [n]\\}\\) is an orthonormal basis under the inner product
  \\[
  \\langle f, g \\rangle = \\mathbb{E}_x[f(x)g(x)] = \\frac{1}{2^n} \\sum_{x \\in \\{0,1\\}^n} f(x)g(x),
  \\]
  where \\(x\\) is uniformly random in \\(\\{0,1\\}^n\\).

**Orthonormality proof sketch**: To show \\(\\langle \\chi_S, \\chi_T \\rangle = \\delta_{S,T}\\):
- When \\(S = T\\): \\(\\chi_S(x)^2 = 1\\) for all \\(x\\), so \\(\\mathbb{E}[\\chi_S^2] = 1\\).
- When \\(S \\neq T\\): Let \\(i \\in S \\triangle T\\) (the symmetric difference). For each assignment to coordinates outside \\(\\{i\\}\\), flipping \\(x_i\\) flips the sign of \\(\\chi_S(x)\\chi_T(x)\\). Since exactly half the inputs have \\(x_i = 0\\) and half have \\(x_i = 1\\), the contributions cancel, giving \\(\\mathbb{E}[\\chi_S \\chi_T] = 0\\).

- Every function can be expanded as
  \\[
  f(x) = \\sum_{S \\subseteq [n]} \\hat f(S) \\chi_S(x).
  \\]

- The Fourier coefficient for subset \\(S\\) is exactly the expectation noted in the Lean comment:
  \\[
  \\hat f(S) = \\mathbb{E}_x\\big[f(x)\\,\\chi_S(x)\\big].
  \\]

Intuitively, \\(\\chi_S\\) measures the parity of \\(x\\) on the coordinates in \\(S\\). Multiplying by \\(\\chi_S(x)\\) and averaging over all \\(x\\) tells us how much of that parity pattern is present in \\(f\\). Large coefficients indicate that \\(f\\) correlates with the parity on \\(S\\).

Finally, the **Fourier degree** (or simply **degree**) of a function \\(f : \\{0,1\\}^n \\to \\mathbb{R}\\) is the largest size \\(|S|\\) for which \\(\\hat f(S)\\neq 0\\). This is the maximum order of parity interaction appearing in the Fourier expansion. For a Boolean function \\(f : \\{0,1\\}^n \\to \\{0,1\\}\\), we treat the output as real-valued (0 or 1) and apply the same definition. By convention, the constant zero function has degree 0 (or sometimes −∞).

## Summary

- \\(\\chi_S(x)\\) is defined as \\((-1)^{|\\{i \\in S : x_i = 1\\}|}\\), computed via a parity test.
- It always returns \\(+1\\) or \\(-1\\).
- The characters \\(\\chi_S\\) form an orthonormal Fourier basis on the Boolean cube.
- Fourier coefficients measure correlation with parity patterns.
- The degree of a Boolean function is the largest set size with a nonzero Fourier coefficient.
`;

sectionContent[4] = `# Section 4: Fourier Coefficients, Degree, and Sensitivity

This section introduces two definitions in Lean:

\`\`\`lean
noncomputable def fourier_coeff {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℝ :=
  (Finset.sum Finset.univ (fun x => (if f x then 1 else 0) * chi S x)) / 2^n

noncomputable def degree {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.sup (Finset.filter (fun S => fourier_coeff f S ≠ 0) Finset.univ) Finset.card
\`\`\`

### Lean syntax walkthrough of the two definitions

There are no tactics in these snippets (no \`by\`, \`simp\`, \`ring\`, etc.). Both lines are *definitions* written in term‑style Lean. Here is a Lean‑focused explanation of every construct and symbol you see:

- \`noncomputable\` tells Lean this definition may rely on classical choice or real‑number operations that are not algorithmically computable. It allows the definition but marks it as non‑computable code.
- \`def\` introduces a new constant with a name and a type.
- \`fourier_coeff\` / \`degree\` are the names being defined.
- \`{n : ℕ}\` is an **implicit argument**: \`n\` is a natural number (type \`ℕ\`), and Lean can usually infer it from context. Curly braces mean you don’t have to pass \`n\` explicitly.
- \`(f : (Fin n → Bool) → Bool)\` is an explicit argument. The type \`(Fin n → Bool)\` is the type of Boolean strings of length \`n\` (functions from \`Fin n\` to \`Bool\`), so \`f\` is a Boolean function on \`n\` bits.
- \`(S : Finset (Fin n))\` is another explicit argument: \`S\` is a finite set of indices from \`Fin n\`.
- \`: ℝ\` or \`: ℕ\` after the arguments is the **result type** of the definition.
- \`:=\` introduces the **definition body** (the term that has the given type).
- \`Finset\` is Lean’s finite‑set type (with decidable membership and finiteness baked in).
- \`Finset.univ\` is the universal finite set over a finite type. Here, \`Finset.univ\` is the set of *all* \`x : Fin n → Bool\` in the sum, or all \`S : Finset (Fin n)\` in the \`filter\`.
- \`Finset.sum\` is the finite sum operator: \`Finset.sum A g\` means \`∑ x in A, g x\`.
- \`fun x => ...\` is a lambda (anonymous function). So \`fun x => ...\` defines the summand for each \`x\`.
- \`if f x then 1 else 0\` is Lean’s \`if-then-else\` expression, here returning a real number. Because the target type is \`ℝ\`, the numerals \`1\` and \`0\` are interpreted as real numbers.
- \`*\` is multiplication in \`ℝ\`, coming from the instance \`Mul ℝ\`.
- \`chi S x\` is an application of the previously‑defined \`chi\` to \`S\` and \`x\`.
- \`/\` is division in \`ℝ\`.
- \`2^n\` uses \`^\` (power). Here the base \`2\` is coerced into \`ℝ\`, and the exponent \`n\` is a natural number, so the result is a real number.
- \`Finset.sup\` computes the supremum (maximum) of a function over a finite set, in a lattice (here \`ℕ\`).
- \`Finset.filter (fun S => ...) Finset.univ\` filters a finite set by a predicate. The predicate is \`fun S => fourier_coeff f S ≠ 0\`.
- \`≠\` is not‑equal. Since \`fourier_coeff f S : ℝ\`, the comparison is in \`ℝ\`.
- \`Finset.card\` is the cardinality function on finite sets. As a function, it is applied by \`Finset.sup\` to each \`S\`.

Below is a web‑tutorial explanation of what these definitions mean and how they connect to sensitivity.

---

## 1. Boolean functions as real‑valued functions

A Boolean function \`f : (Fin n → Bool) → Bool\` takes an \`n\`‑bit input and returns a Boolean output. The Fourier analysis of Boolean functions usually works with real‑valued functions, so the code converts the output to a real number using:

\`\`\`lean
(if f x then 1 else 0)
\`\`\`

This maps \`false ↦ 0\` and \`true ↦ 1\`. (Sometimes the literature uses \`{-1, +1}\` instead; here we stick to \`{0,1}\` because that's exactly what the code does.)

---

## 2. Fourier coefficients in the code

### The definition

\`\`\`lean
fourier_coeff f S =
  (sum over all x) ((if f x then 1 else 0) * chi S x) / 2^n
\`\`\`

This is the average value of \`f(x) * chi_S(x)\` over all inputs \`x\`.

### What is \`chi S x\`?

\`chi S x\` is the parity character defined in **Section 3**:

\`\`\`lean
chi S x = (-1)^{|{i ∈ S : x i = true}|}
\`\`\`

It returns \`+1\` if an even number of coordinates in \`S\` are true, and \`-1\` if odd. This is the standard Fourier basis function for Boolean analysis.

### Expectation interpretation

The Fourier coefficient is the expectation of \`f(x) · χ_S(x)\` under the uniform distribution:

\`\`\`
fourier_coeff f S = 𝔼_x[f(x) · χ_S(x)] = (1/2^n) · Σ_{x ∈ {0,1}^n} f(x) · χ_S(x)
\`\`\`

where \`f(x)\` is treated as 0 or 1 (the \`{0,1}\` encoding). This measures how much \`f\` "aligns" with the parity pattern on \`S\`.

---

## 3. Degree from Fourier support

The second definition uses the Fourier coefficients to define the **degree**:

\`\`\`lean
degree f =
  sup (card S) over all S with fourier_coeff f S ≠ 0
\`\`\`

In words:

- Look at every subset \`S\` of variables.
- Keep only those where the Fourier coefficient is nonzero.
- Take the maximum size of such a set.

This is exactly the **Fourier degree**: the largest subset size for which the Fourier expansion has a non‑zero coefficient.

**Convention for edge cases**: If \`f\` is the constant zero function, then all Fourier coefficients are zero, and \`Finset.sup\` over an empty set returns \`0\` (the lattice bottom for \`ℕ\`). So the constant zero function has degree 0. The constant one function has \`fourier_coeff f ∅ = 1 ≠ 0\` and all other coefficients zero, so it also has degree 0.

### Intuition

- Low degree means the function is well‑approximated by small‑interaction terms (few variables at a time).
- High degree means the function needs large, global parity patterns to describe it.

---

## 4. Connection to sensitivity

**Sensitivity** measures how many single‑bit flips can change the function's value at a given input. For a Boolean function \`f\`, the sensitivity at input \`x\` counts how many coordinates \`i\` satisfy:

\`\`\`
  f(x) ≠ f(x with bit i flipped)
\`\`\`

The maximum of that count over all \`x\` is the sensitivity of \`f\`.

### Why Fourier degree matters

Fourier analysis provides a powerful bridge between algebraic structure and combinatorial measures like sensitivity:

- A nonzero Fourier coefficient on a large set \`S\` means the function depends (in a parity sense) on many variables at once.
- That kind of global dependence tends to force the function to be sensitive to bit flips.

More concretely:

- If a function has **high Fourier degree**, then there must be some input where many variables matter. That often implies higher sensitivity.
- Conversely, if the function has very low sensitivity everywhere, the Fourier expansion tends to concentrate on small sets, leading to low degree.

This is the basic intuition behind the **Sensitivity Conjecture** (now a theorem, proved by Huang 2019):

**Theorem (Sensitivity Conjecture)**: For any Boolean function \`f : {0,1}^n → {0,1}\`,
\`\`\`
sensitivity(f) ≥ √(degree(f))
\`\`\`

This says that high Fourier degree implies high sensitivity. The Lean formalization in this project proves exactly this inequality. The converse direction (\`degree(f) ≤ sensitivity(f)^2\`) is easier and was known earlier; together they show that sensitivity and degree are polynomially related.

---

## 5. Takeaway

- \`fourier_coeff f S\` is the normalized correlation of \`f\` with the parity character on \`S\`.
- \`degree f\` is the maximum size of a subset with a nonzero Fourier coefficient.
- High degree captures global interactions among many variables.
- Sensitivity captures how fragile \`f\` is to individual bit flips.
- Fourier degree and sensitivity are tightly linked, making Fourier analysis a natural tool for studying sensitivity.

---

If you want, the next step is to look at how \`chi S x\` is defined in the Lean code and how the \`{0,1}\` output encoding compares to the more common \`{−1,+1}\` normalization—this will clarify constants and sign conventions in later lemmas.
`;

sectionContent[5] = `# Section 5: Type Equivalences for the Huang Matrix Indexing

This section defines three explicit type equivalences in Lean. They are not just abstract conveniences: they are exactly the "index bookkeeping" needed to describe the recursive block structure of the Huang matrix when rows/columns are indexed by Boolean hypercube vertices.

Below is what each definition does, how it works, and why it matters for the Huang matrix.

---

## 1) \`boolProdEquivSum_custom\` : \`Bool × α ≃ α ⊕ α\`

**Lean definition**
\`\`\`lean
def boolProdEquivSum_custom {α : Type*} : Bool × α ≃ α ⊕ α where
  toFun := fun p => if p.1 then Sum.inr p.2 else Sum.inl p.2
  invFun := fun s => match s with
    | Sum.inl a => (false, a)
    | Sum.inr a => (true, a)
  left_inv := by
    rintro ⟨ _ | _, _ ⟩ <;> simp +decide
  right_inv := by
    rintro (a | a) <;> rfl
\`\`\`

### What it means
- A pair \`(b, a)\` with \`b : Bool\` and \`a : α\` can be seen as **"choose left or right copy of α"** depending on \`b\`.
- Thus \`Bool × α\` is equivalent to \`α ⊕ α\` (a sum of two copies of \`α\`).

### How it works
- **Forward map**: send \`(true, a)\` to \`Sum.inr a\` and \`(false, a)\` to \`Sum.inl a\`.
- **Inverse map**: send \`Sum.inl a\` back to \`(false, a)\`, and \`Sum.inr a\` back to \`(true, a)\`.
- The proofs \`left_inv\` and \`right_inv\` show these two functions undo each other.

### Lean details (constructs, syntax, tactics)
- \`def ... : ... where\` defines a structure instance by giving its fields. Here the structure is \`Equiv\`, with fields \`toFun\`, \`invFun\`, \`left_inv\`, \`right_inv\`.
- \`{α : Type*}\` uses implicit arguments and universe polymorphism. \`Type*\` means "any universe level."
- \`Bool × α ≃ α ⊕ α\` uses \`×\` for product types and \`⊕\` for sum types; \`≃\` is the type of equivalences (\`Equiv\`).
- \`toFun := fun p => ...\` uses a lambda; \`p.1\` and \`p.2\` are projections from a pair.
- \`if p.1 then ... else ...\` is boolean \`if\`, and \`Sum.inl\`/\`Sum.inr\` are constructors for the left/right sum.
- \`invFun := fun s => match s with | Sum.inl a => ... | Sum.inr a => ...\` is pattern matching; each branch returns a pair \`(Bool, α)\`.
- \`left_inv := by ...\` and \`right_inv := by ...\` enter tactic mode with \`by\`, producing proofs.
- \`rintro ⟨ _ | _, _ ⟩\` is a pattern-matching intro in tactic mode:
  - \`⟨..., ...⟩\` matches a pair.
  - \`_ | _\` is a pattern for \`Bool\` (cases \`false | true\`), so this splits on the boolean component.
  - The second \`_\` matches the \`α\` component.
- \`<;>\` is "tactic sequencing on all goals." It applies the following tactic to each goal produced by \`rintro\`.
- \`simp +decide\` runs the simplifier, and \`+decide\` adds \`decide\` lemmas to solve boolean conditions.
- \`rintro (a | a)\` pattern-matches on a sum (left or right). \`rfl\` closes goals by reflexivity of definitional equality.

### Why it matters
When you split the Boolean hypercube by the first coordinate, every vertex is "either in the 0-slice or the 1-slice." The sum type \`α ⊕ α\` captures exactly this "either/or" split, which is perfect for block matrices: the two summands correspond to two diagonal blocks.

---

## 2) \`finSuccEquiv_custom\` : \`(Fin (n+1) → α) ≃ α × (Fin n → α)\`

**Lean definition**
\`\`\`lean
def finSuccEquiv_custom (n : ℕ) (α : Type*) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun f := (f 0, f ∘ Fin.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    ext i
    refine Fin.cases ?_ ?_ i <;> simp
  right_inv p := by
    ext <;> simp
\`\`\`

### What it means
- A function \`f : Fin (n+1) → α\` is completely determined by:
  1) its value at \`0\`, and
  2) its values on the remaining indices \`{1, …, n}\` (which are in bijection with \`Fin n\`).
- So such a function is equivalent to a pair \`(α, Fin n → α)\`.

### How it works
- **Forward map**: \`f ↦ (f 0, f ∘ Fin.succ)\`.
  - \`Fin.succ : Fin n → Fin (n+1)\` is the canonical injection that maps \`i\` to \`i+1\`.
  - So \`f ∘ Fin.succ\` is the "tail" of \`f\`, giving values at indices \`1, 2, ..., n\`.
- **Inverse map**: \`Fin.cons p.1 p.2\` rebuilds a function from a head value \`p.1\` and tail \`p.2\`.
  - \`Fin.cons : α → (Fin n → α) → (Fin (n+1) → α)\` prepends a head to a tail.
- The proof uses \`Fin.cases\` to split the index into "zero" vs. "successor."
  - \`Fin.cases\` is case analysis: given a goal for \`Fin (n+1)\`, prove it for \`0\` and for \`succ i\`.

### Lean details (constructs, syntax, tactics)
- \`(Fin (n + 1) → α) ≃ α × (Fin n → α)\` is an \`Equiv\` between function types and a product.
- \`ℕ\` is the type of natural numbers in Lean. \`n + 1\` is syntactic sugar for \`Nat.succ n\`.
- \`toFun f := (f 0, f ∘ Fin.succ)\` uses function application and composition:
  - \`f 0\` is the value of \`f\` at the element \`0 : Fin (n+1)\`.
  - \`∘\` is function composition; \`f ∘ Fin.succ\` is a function \`Fin n → α\`.
- \`invFun p := Fin.cons p.1 p.2\` uses \`Fin.cons\`, which constructs a function on \`Fin (n+1)\` by giving the value at \`0\` and a function on successors.
- \`left_inv f := by\` and \`right_inv p := by\` are proofs in tactic mode.
- \`ext i\` invokes the extensionality tactic for functions: to show two functions are equal, it introduces an index \`i\` and reduces to pointwise equality.
- \`refine Fin.cases ?_ ?_ i\` performs case analysis on \`i : Fin (n+1)\`:
  - The two goals correspond to the \`0\` case and the \`succ\` case.
  - \`?_\` are placeholders for the subproofs; Lean creates new goals for them.
- \`<;> simp\` simplifies both generated goals. \`simp\` uses definitional reductions like \`Fin.cases\` and \`Fin.cons\` to show the equalities.
- \`right_inv\` uses \`ext\` with no explicit binder (\`ext\`) and \`simp\` to discharge the pair equality by componentwise simplification.

### Why it matters
Vertices of the Boolean hypercube of dimension \`n+1\` are functions \`Fin (n+1) → Bool\`. This equivalence lets you pull out the first coordinate explicitly as a separate piece. It is the fundamental "peel off the first bit" operation.

---

## 3) \`finSuccEquiv_huang_custom\` : \`(Fin (n+1) → Bool) ≃ (Fin n → Bool) ⊕ (Fin n → Bool)\`

**Lean definition**
\`\`\`lean
def finSuccEquiv_huang_custom (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Fin n → Bool) ⊕ (Fin n → Bool) :=
  Equiv.trans
    (finSuccEquiv_custom n Bool)
    (boolProdEquivSum_custom)
\`\`\`

### What it means
This simply **composes** the previous two equivalences:
1) First, split a Boolean function on \`Fin (n+1)\` into \`(Bool, Fin n → Bool)\`.
2) Then turn \`(Bool, Fin n → Bool)\` into a sum of two copies of \`Fin n → Bool\`.

So we get a clean equivalence:

\`\`\`
(Fin (n+1) → Bool)  ≃  (Fin n → Bool) ⊕ (Fin n → Bool)
\`\`\`

**Summand ordering convention**: The composition sends:
- \`(false, tail)\` to \`Sum.inl tail\` — the "left" or "top" block
- \`(true, tail)\` to \`Sum.inr tail\` — the "right" or "bottom" block

This means vertices with first coordinate \`false\` go to \`Sum.inl\`, and vertices with first coordinate \`true\` go to \`Sum.inr\`. This ordering determines which block of the matrix corresponds to which summand.

### Lean details (constructs, syntax)
- The return type is an explicit \`Equiv\` between function types and a sum type.
- \`:=\` assigns the definition body. The right-hand side is an expression (not tactic mode).
- \`Equiv.trans\` composes equivalences: if \`e₁ : A ≃ B\` and \`e₂ : B ≃ C\`, then \`Equiv.trans e₁ e₂ : A ≃ C\`.
- \`(finSuccEquiv_custom n Bool)\` instantiates the generic equivalence at \`α := Bool\`.
- \`(boolProdEquivSum_custom)\` is used with its implicit parameter \`α\` inferred as \`Fin n → Bool\`.
- Indentation and parentheses are purely syntactic; they group arguments and make the composition readable.

### Why it matters for the Huang matrix
The Huang matrix \`A_n\` is indexed by Boolean hypercube vertices, i.e.

\`\`\`
indices_n := Fin n → Bool
\`\`\`

The recursion for \`A_{n+1}\` is a **block matrix** with four \`2^n × 2^n\` blocks:

- top-left: \`A_n\`
- top-right: \`I\`
- bottom-left: \`I\`
- bottom-right: \`-A_n\`

To even *state* this block structure in Lean, you must identify the index set for dimension \`n+1\` with **two copies** of the index set for dimension \`n\`.

That is exactly what \`finSuccEquiv_huang_custom\` gives you:

\`\`\`
indices_{n+1}  ≃  indices_n ⊕ indices_n
\`\`\`

Once you have this equivalence, you can:
- reindex rows and columns of \`A_{n+1}\` into "upper" and "lower" halves,
- align those halves with the two copies of \`indices_n\`, and
- express the recursion as a block matrix in a type-correct way.

Without this explicit equivalence, the block recursion is only informal. With it, Lean can treat \`A_{n+1}\` as a matrix indexed by a sum type and accept the block decomposition.

---

## Summary
- \`boolProdEquivSum_custom\` turns a Boolean choice into a sum type.
- \`finSuccEquiv_custom\` peels off the first coordinate of a function on \`Fin (n+1)\`.
- \`finSuccEquiv_huang_custom\` combines both to split the Boolean hypercube into two copies of the \`n\`-dimensional hypercube.

This is precisely the indexing trick needed to define the Huang matrix recursion as a block matrix in Lean.
`;

sectionContent[6] = `# Section 6: Recursive Block Definition of the Huang Matrix

This section defines a family of matrices \`huang_matrix (n : ℕ)\` over \`ℝ\` indexed by Boolean vectors of length \`n\`.

\`\`\`lean
def huang_matrix (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  match n with
  | 0 => 0
  | n + 1 => Matrix.reindex (finSuccEquiv_huang_custom n).symm (finSuccEquiv_huang_custom n).symm
      (Matrix.fromBlocks (huang_matrix n) (1 : Matrix _ _ ℝ) (1 : Matrix _ _ ℝ) (-huang_matrix n))
\`\`\`

Lean parsing notes for the definition above:

- \`def\` introduces a new constant. Here \`huang_matrix\` is a definition (not a theorem) that computes a matrix from \`n\`.
- \`(n : ℕ)\` is a binder with an explicit type annotation; \`ℕ\` is Lean's natural numbers.
- \`:\` introduces the return type. \`Matrix α β ℝ\` is the type of matrices with row index type \`α\`, column index type \`β\`, and entries in \`ℝ\`.
- \`:=\` separates the name/signature from the defining expression.
- \`match n with\` is Lean's pattern matching syntax; the subsequent \`|\` branches are the cases.
- \`| 0 => 0\` uses the numeral \`0\` overloaded at the matrix type; Lean infers it as the zero matrix because the expected type is \`Matrix (Fin 0 → Bool) (Fin 0 → Bool) ℝ\`.
- \`| n + 1 => ...\` is the successor case; \`n\` is a new binder for the predecessor in this branch.
- The two occurrences of \`.symm\` are field projections on an equivalence: if \`e : α ≃ β\`, then \`e.symm : β ≃ α\`.
- \`Matrix.reindex\` changes row/column index types using equivalences; it is not changing entries, just how indices are named.
- \`Matrix.fromBlocks A B C D\` expects four matrices of compatible sizes and forms a 2×2 block matrix.
- The \`(1 : Matrix _ _ ℝ)\` are type ascriptions; \`_\` is a placeholder for inferred index types, and \`1\` is the multiplicative identity matrix at that type.
- \`-huang_matrix n\` is unary negation in the additive group of matrices.

Below is a web-style explanation of the recursive block matrix construction.

## 1. What the type says

\`Matrix (Fin n → Bool) (Fin n → Bool) ℝ\` is a square matrix whose rows and columns are indexed by functions \`Fin n → Bool\`, i.e. Boolean vectors of length \`n\`.

So for each \`n\`, \`huang_matrix n\` is a \`2^n × 2^n\` real matrix, but it is indexed by *functions* rather than integer indices.

**Why 2^n?** The type \`Fin n → Bool\` is a function type with \`2^n\` elements: there are 2 choices (true/false) for each of the \`n\` positions. Lean's \`Fintype\` instance computes \`Fintype.card (Fin n → Bool) = 2^n\` via \`Fintype.card_pi\`.

Lean syntax notes for this type:

- \`Fin n\` is the finite type \`{0, 1, ..., n-1}\`. The arrow \`→\` is the function type constructor, so \`Fin n → Bool\` is the type of Boolean-valued functions on \`Fin n\`.
- The function arrow is right-associative, but here it is parenthesized to make the matrix indices explicit.
- \`Matrix\` in Lean is a type synonym for functions \`α → β → R\`, so \`Matrix (Fin n → Bool) (Fin n → Bool) ℝ\` is really \`(Fin n → Bool) → (Fin n → Bool) → ℝ\`.
- The \`ℝ\` is \`Real\`, imported from Lean's standard library; it signals we are working in the real matrix ring.

## 2. Base case: \`n = 0\`

\`\`\`lean
| 0 => 0
\`\`\`

When \`n = 0\`, the index type \`Fin 0 → Bool\` has exactly one element (the empty function), so the matrix is \`1 × 1\`. The definition returns \`0\`, the zero matrix of that size.

Lean parsing notes for the base case:

- The pattern \`0\` matches the literal zero constructor of \`ℕ\`.
- The \`=>\` arrow separates pattern from branch expression.
- The literal \`0\` is polymorphic: it is from the \`OfNat\` typeclass and is specialized to the zero matrix because of the expected type of the match expression.

**Note**: This means \`H_0 = [0]\`, the 1×1 zero matrix. This satisfies \`H_0² = 0·I\` (since 0² = 0 and 0·I = 0 for the 1×1 identity). The formula \`H_n² = n·I\` holds with \`n = 0\`.

## 3. Recursive case: \`n + 1\`

\`\`\`lean
| n + 1 => Matrix.reindex ... (Matrix.fromBlocks ...)
\`\`\`

The recursive step builds \`huang_matrix (n+1)\` as a **2×2 block matrix**, where each block is itself a matrix indexed by Boolean vectors of length \`n\`.

Lean parsing notes for the successor case:

- The pattern \`n + 1\` is syntactic sugar for \`Nat.succ n\`, so \`n\` is bound as the predecessor.
- Because the branch expression is expected to have type \`Matrix (Fin (n+1) → Bool) (Fin (n+1) → Bool) ℝ\`, Lean will infer index types for \`fromBlocks\` and \`reindex\` accordingly.
- Parentheses are used to group the arguments to \`Matrix.reindex\` and \`Matrix.fromBlocks\`; function application is left-associative in Lean.

### 3.1 The block structure

The key expression is:

\`\`\`lean
Matrix.fromBlocks (huang_matrix n) (1 : Matrix _ _ ℝ)
                  (1 : Matrix _ _ ℝ) (-huang_matrix n)
\`\`\`

\`Matrix.fromBlocks A B C D\` builds the block matrix

\`\`\`
[ A  B ]
[ C  D ]
\`\`\`

Here:

- \`A\` is \`huang_matrix n\`
- \`D\` is \`-huang_matrix n\`
- \`B\` and \`C\` are both \`1\`, the identity matrix of appropriate size

**Lean notation**: In Lean's matrix library, \`1 : Matrix α α R\` denotes the identity matrix (diagonal 1s, off-diagonal 0s), not the all-ones matrix. This is the multiplicative identity in the matrix ring. The type annotation \`: Matrix _ _ ℝ\` ensures Lean infers the correct size from context.

Lean syntax notes for this block expression:

- \`Matrix.fromBlocks\` expects all four matrices to have the same row/column index types within their blocks; the underscores \`_\` are placeholders that Lean fills in using unification.
- The type ascription \`(1 : Matrix _ _ ℝ)\` is required because without it \`1\` could be any type with a \`One\` instance; the ascription pins it to a matrix identity.
- Unary \`-\` is notation for \`Neg.neg\`; its matrix instance negates every entry.

So the recursive definition is:

\`\`\`
H_{n+1} = [  H_n     I ]
          [   I   -H_n ]
\`\`\`

This is a classic recursive block construction, similar in spirit to Hadamard-type recurrences but with identity matrices on the off-diagonals and a sign flip on the bottom-right block.

### 3.2 Where the indices live

\`fromBlocks\` naturally produces a matrix indexed by a *sum type* of indices:

\`\`\`
(Fin n → Bool) ⊕ (Fin n → Bool)
\`\`\`

That is, it expects row and column indices to be either a "left" index (top block) or a "right" index (bottom block).

But we want the final result indexed by \`Fin (n+1) → Bool\` (Boolean vectors of length \`n+1\`).

### 3.3 Reindexing with an equivalence

That is why we wrap the block matrix with \`Matrix.reindex\`:

\`\`\`lean
Matrix.reindex (finSuccEquiv_huang_custom n).symm
               (finSuccEquiv_huang_custom n).symm
               (Matrix.fromBlocks ...)
\`\`\`

- \`finSuccEquiv_huang_custom n\` is an equivalence between
  \`Fin (n+1) → Bool\` and \`(Fin n → Bool) ⊕ (Fin n → Bool)\`
  (defined in **Section 5**). It splits a length-\`n+1\` Boolean vector into the first bit choosing left (\`Sum.inl\` for \`false\`) or right (\`Sum.inr\` for \`true\`), with the remaining \`n\` bits giving the index within that block.
- The \`.symm\` uses the inverse direction because \`fromBlocks\` already lives in the sum-indexed world.

So \`reindex\` converts the block-indexed matrix into one indexed by Boolean vectors of length \`n+1\`.

Lean syntax notes for \`reindex\` and equivalences:

- \`⊕\` is \`Sum\` (disjoint union). Lean writes \`Sum.inl\` and \`Sum.inr\` for the two injections.
- An equivalence \`e : α ≃ β\` is a structure with fields \`toFun\`, \`invFun\`, and proofs of left/right inverse; \`e.symm\` flips the direction.
- \`Matrix.reindex e₁ e₂ M\` takes two equivalences for rows and columns and produces a matrix with new indices; it transports the function \`M\` along those equivalences.
- The two \`finSuccEquiv_huang_custom n\` calls are identical but used for rows and columns separately; the symmetry is explicit in the code.

## 4. Why this is a recursive block definition

Putting it all together:

- \`H_0\` is the zero 1×1 matrix.
- \`H_{n+1}\` is built from \`H_n\` in a 2×2 block pattern:
  - top-left is \`H_n\`
  - bottom-right is \`-H_n\`
  - off-diagonals are identity matrices
- a reindexing step converts block indices into Boolean-vector indices

This is a canonical recursive block matrix definition: you double the dimension by stacking four blocks, two of which are the previous matrix (one with a sign flip), and two of which are identity matrices.

## 5. The accompanying statement

The comment at the end hints at a key property of the Huang matrices:

\`\`\`lean
/-
The square of the Huang matrix A_n is n times the identity matrix.
-/
\`\`\`

So the recursion is set up to make \`H_n^2 = n * I\` true for all \`n\`. The block form makes it possible to prove this by induction, since block multiplication decomposes into the same four-block pattern.

---

**Summary:** \`huang_matrix\` is defined recursively by a 2×2 block construction, with off-diagonal identities, a sign flip on the bottom-right, and a reindexing step to convert the block sum indices into Boolean-vector indices. This is the Lean encoding of a structured matrix recurrence that supports an inductive proof of its algebraic properties.
`;

sectionContent[7] = `# Section 7: Why A² = nI for the Huang Matrix, and What That Means for Eigenvalues

This section proves a key identity for the Huang matrix \`huang_matrix n\`:

\`\`\`
(huang_matrix n)^2 = n * I
\`\`\`

where \`I\` is the identity matrix of the same size. In Lean, this appears as:

\`\`\`lean
theorem huang_matrix_sq (n : ℕ) :
  (huang_matrix n) ^ 2 = (n : ℝ) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ)
\`\`\`

**Lean notation**:
- \`theorem\` introduces a named lemma with a statement and a proof
- \`(n : ℕ)\` declares the input \`n\` as a natural number; \`:\` is type ascription
- \`^ 2\` is \`pow\` on matrices: \`M ^ 2 = M ⬝ M\` (matrix multiplication)
- \`(n : ℝ)\` coerces the natural number \`n\` to a real number
- \`•\` is scalar multiplication (smul): \`r • M\` multiplies every entry of matrix \`M\` by scalar \`r\`
- \`1 : Matrix _ _ ℝ\` is the identity matrix (diagonal 1s, off-diagonal 0s), not all-ones
- \`Matrix (Fin n → Bool) (Fin n → Bool) ℝ\` is the type of real matrices indexed by \`Fin n → Bool\` on rows and columns
- \`Fin n\` is the type \`{0, 1, ..., n-1}\`; \`Fin n → Bool\` is an \`n\`-bit string
- Parentheses \`(...)\` control precedence; Lean is explicit about grouping

The matrix is indexed by \`Fin n -> Bool\`, so it has size \`2^n x 2^n\`. The proof uses induction on \`n\` and the special block structure of the Huang matrix.

## Big picture

The Huang matrix is built recursively using a block form. At a high level, if we write

\`\`\`
A_{n+1} = [ A_n   I
            I    -A_n ]
\`\`\`

then squaring this block matrix gives

\`\`\`
A_{n+1}^2 = [ A_n^2 + I   0
              0     A_n^2 + I ]
\`\`\`

By the induction hypothesis, \`A_n^2 = n I\`, so each diagonal block becomes \`(n+1) I\`. That yields

\`\`\`
A_{n+1}^2 = (n+1) I
\`\`\`

This is exactly what the Lean proof encodes.

## Step-by-step reading of the Lean proof

### 1) Induction on n

The proof starts with:

\`\`\`lean
induction' n with n ih;
\`\`\`

- Base case \`n = 0\`: the matrix \`H_0\` is the 1×1 zero matrix \`[0]\` (see Section 6). Its square is \`[0]\`, and \`0 • I = [0]\`, so \`H_0² = 0 • I\` ✓
- Inductive step: assume the result holds for \`n\`, prove it for \`n+1\`.
- \`induction'\` is a Mathlib tactic that performs induction and lets you name the new variable and hypothesis
- \`with n ih\` means: in the inductive step, the predecessor is named \`n\` and the induction hypothesis is named \`ih\`
- The trailing \`;\` lets the following tactic script apply to both the base and inductive cases

### 2) Use the block definition

The Huang matrix is defined recursively. The proof names that definition:

\`\`\`lean
have h_def : huang_matrix (n + 1) =
  Matrix.reindex ... (Matrix.fromBlocks (huang_matrix n) 1 1 (-huang_matrix n)) := by rfl
\`\`\`

Two details:

- \`Matrix.fromBlocks\` builds the block matrix \`[A_n I; I -A_n]\`.
- \`Matrix.reindex\` just reorders indices so the block form matches the indexing by \`(Fin (n+1) -> Bool)\`. It does not change the algebraic content.
- \`have h_def : ... := ...\` introduces a local lemma named \`h_def\` with a proof
- \`:= by rfl\` proves the statement by definitional equality (\`rfl\` = "reflexivity"), which works when both sides unfold to the same definition
- The unary \`-\` on \`huang_matrix n\` is entrywise negation
- \`1\` inside \`fromBlocks\` is the identity matrix at the appropriate size; Lean inserts typeclass instances for matrix operations automatically

### 3) Square the block matrix

The proof then expands the square of the block matrix:

\`\`\`lean
(Matrix.fromBlocks A I I (-A))^2
  = Matrix.fromBlocks ((n+1)•I) 0 0 ((n+1)•I)
\`\`\`

This is the critical calculation. Let's expand the block multiplication explicitly:

\\[
\\begin{bmatrix} A & I \\\\ I & -A \\end{bmatrix}
\\begin{bmatrix} A & I \\\\ I & -A \\end{bmatrix}
= \\begin{bmatrix} A^2 + I & AI - IA \\\\ IA - AI & I + A^2 \\end{bmatrix}
= \\begin{bmatrix} A^2 + I & 0 \\\\ 0 & A^2 + I \\end{bmatrix}
\\]

**Off-diagonal cancellation**: Since \\(AI = IA = A\\) (identity commutes with everything), we have \\(AI + I(-A) = A - A = 0\\).

**Diagonal blocks**: Both diagonal blocks are \\(A^2 + I\\). By the induction hypothesis \\(A^2 = nI\\), so:
\\[
A^2 + I = nI + I = (n+1)I
\\]

Therefore:
\\[
A_{n+1}^2 = \\begin{bmatrix} (n+1)I & 0 \\\\ 0 & (n+1)I \\end{bmatrix} = (n+1)I
\\]

Lean typically achieves this with:
- \`simp\` to rewrite \`A ⬝ I\`, \`I ⬝ A\`, and \`A ⬝ (-A)\` using matrix identities
- \`simp [ih]\` to apply the induction hypothesis \`ih : (huang_matrix n)^2 = (n : ℝ) • I\`
- \`simp\` with \`Matrix.fromBlocks\` multiplication lemmas to reduce off-diagonal blocks to \`0\`
- A ring- or arithmetic-simplification step to turn \`n + 1\` into \`(n + 1 : ℝ)\` after coercions

### 4) Reindexing and extensionality

The remainder of the Lean code uses \`simp\`, \`ext\`, and a case split on \`i = j\` to conclude the final equality after reindexing. This is bookkeeping to align the matrix entries with the identity matrix definition.

- \`ext i j\` uses extensionality: two matrices are equal if all corresponding entries are equal
- A case split is written \`by_cases h : i = j\`; it creates two goals, one with \`h : i = j\` and one with \`h : i ≠ j\`
- In the \`i = j\` case, the goal reduces to the diagonal entry being \`(n+1)\`; in the \`i ≠ j\` case, it reduces to \`0 = 0\`
- \`simp [h]\` or \`simp [h, Matrix.one_apply]\` uses the hypothesis \`h\` to simplify identity-matrix entries
- \`Matrix.reindex\` applies an equivalence of index types; \`simp\` knows it preserves entries up to that equivalence

## Why \\(A^2 = nI\\) matters: eigenvalues

If a square matrix \\(A\\) satisfies \\(A^2 = nI\\), then every eigenvalue \\(\\lambda\\) must satisfy \\(\\lambda^2 = n\\).

**Proof**: If \\(Av = \\lambda v\\) for some nonzero vector \\(v\\), then:
\\[
A^2 v = A(Av) = A(\\lambda v) = \\lambda(Av) = \\lambda^2 v
\\]

But \\(A^2 = nI\\) also implies \\(A^2 v = nv\\). Therefore:
\\[
\\lambda^2 v = nv
\\]

Since \\(v \\neq 0\\), we conclude \\(\\lambda^2 = n\\).

### Consequences

- Over \\(\\mathbb{R}\\), the only possible eigenvalues are \\(+\\sqrt{n}\\) and \\(-\\sqrt{n}\\).
- The spectrum is symmetric: if \\(\\lambda\\) is an eigenvalue, so is \\(-\\lambda\\).
- The matrix is diagonalizable over \\(\\mathbb{R}\\) if it is symmetric. The Huang matrix is symmetric (proved in **Section 12**), so it has an orthonormal eigenbasis with eigenvalues \\(\\pm\\sqrt{n}\\).

## Summary

The proof shows that the Huang matrix is an involution up to scaling: squaring it gives a scalar multiple of the identity. This immediately pins down the eigenvalues to the square roots of \`n\`, which is exactly why the comment at the end of the Lean file says: "The eigenvalues of the Huang matrix square to n."
`;

sectionContent[8] = `# Section 8: Eigenvalues of the Huang Matrix

This section proves a clean characterization of the eigenvalues of the Huang matrix. The key idea is that the matrix squares to a scalar multiple of the identity. From that, any eigenvalue must satisfy a simple quadratic equation.

## The Lean statement

\`\`\`lean
theorem huang_matrix_eigenvalues {n : ℕ} {μ : ℝ}
  (h : Module.End.HasEigenvalue (Matrix.toLin' (huang_matrix n)) μ) :
  μ ^ 2 = n := by
  ...
\`\`\`

Read this as: for any natural number \`n\` and real number \`μ\`, if \`μ\` is an eigenvalue of the linear map corresponding to \`huang_matrix n\`, then \`μ^2 = n\`.

Lean syntax notes:
- \`theorem\` introduces a named proposition with a proof.
- \`{n : ℕ} {μ : ℝ}\` are implicit arguments (Lean can infer them). \`ℕ\` is naturals, \`ℝ\` reals.
- \`(h : Module.End.HasEigenvalue ...)\` is an explicit argument named \`h\` with its type.
- \`Matrix.toLin'\` coerces a matrix into a linear map; \`huang_matrix n\` is the matrix at size \`n\`.
- \`μ ^ 2\` is exponentiation in a semiring; \`:\` separates the statement from its proof.
- \`:= by\` starts a tactic proof block.

## Mathematical idea

Let \`A\` be the Huang matrix. The earlier lemma \`huang_matrix_sq n\` says

\`\`\`
A^2 = n I.
\`\`\`

If \`v\` is an eigenvector for eigenvalue \`μ\`, then

\`\`\`
A v = μ v.
\`\`\`

Apply \`A\` again:

\`\`\`
A^2 v = A (A v) = A (μ v) = μ (A v) = μ (μ v) = μ^2 v.
\`\`\`

But \`A^2 = n I\`, so

\`\`\`
A^2 v = n v.
\`\`\`

Therefore

\`\`\`
μ^2 v = n v.
\`\`\`

Since \`v\` is a nonzero eigenvector, we can cancel \`v\` and conclude

\`\`\`
μ^2 = n.
\`\`\`

This is exactly what the theorem states: every eigenvalue must be a square root of \`n\` (over the reals, this means \`μ = ±√n\`).

## How the Lean proof mirrors the math

### 1) Extract an eigenvector

\`\`\`lean
obtain ⟨ v, hv ⟩ := h.exists_hasEigenvector;
\`\`\`

From \`HasEigenvalue\`, we get an eigenvector \`v\` with proof \`hv\` that it is nonzero and satisfies the eigenvector equation.

Lean syntax notes:
- \`obtain ⟨ v, hv ⟩ := ...\` destructs an existential or sigma type, binding the witness \`v\` and proof \`hv\`.
- \`h.exists_hasEigenvector\` is a lemma: from \`HasEigenvalue\`, you can extract a \`HasEigenvector\`.
- \`⟨ v, hv ⟩\` is tuple/constructor syntax for dependent pairs.

### 2) Apply the squared matrix identity

\`\`\`lean
have h_sq : (Matrix.toLin' (huang_matrix n)) (Matrix.toLin' (huang_matrix n) v)
  = (n : ℝ) • v := by
  convert congr_arg (fun x => x.mulVec v) <| huang_matrix_sq n using 1;
  · simp +decide [sq];
  · simp +decide [Matrix.smul_eq_diagonal_mul];
\`\`\`

Here the proof applies the matrix identity \`A^2 = n I\` to the vector \`v\`. The \`convert\` step rewrites the identity in the form needed for \`mulVec\`, and \`simp\` handles the algebraic reshaping.

Lean syntax notes:
- \`have h_sq : ... := by\` introduces a local lemma named \`h_sq\` with an explicit type.
- \`(n : ℝ)\` is a type ascription, coercing \`n\` from \`ℕ\` to \`ℝ\`.
- \`•\` is scalar multiplication.
- \`convert\` asks Lean to change the goal to a definitionaly equal one; \`using 1\` tells it how many definitional reductions are allowed.
- \`congr_arg (fun x => x.mulVec v)\` applies a function to both sides of an equation; here it maps a matrix to its \`mulVec\` action on \`v\`.
- \`<|\` is right-associative application (same as parentheses).
- \`simp\` is the simplifier; \`+decide\` allows it to discharge decidable propositions; \`[sq]\` and \`[Matrix.smul_eq_diagonal_mul]\` are simp-lemma sets.

### 3) Use the eigenvector equation

\`\`\`lean
have h_eigen : (Matrix.toLin' (huang_matrix n)) v = μ • v := by
  cases hv; aesop;
\`\`\`

This is the direct eigenvector equation \`A v = μ v\`.

Lean syntax notes:
- \`cases hv\` splits the \`HasEigenvector\` proof into its fields (equation and nonzero).
- \`aesop\` is an automation tactic that solves straightforward goals by combining lemmas.

### 4) Combine both and cancel the vector

\`\`\`lean
simp_all +decide [sq];
exact smul_left_injective _ hv.2 <| by
  simpa [mul_assoc, smul_smul] using h_sq;
\`\`\`

After rewriting, Lean shows \`μ^2 • v = n • v\`. The lemma \`smul_left_injective\` lets us cancel the nonzero vector \`v\` (the nonzero proof is \`hv.2\`), leaving \`μ^2 = n\`.

Lean syntax notes:
- \`simp_all\` simplifies using all local hypotheses; \`+decide\` again lets it close decidable side-goals.
- \`exact\` finishes the goal by giving a term/proof.
- \`smul_left_injective _ hv.2\` says scalar multiplication by a nonzero vector is injective; \`hv.2\` is the second component of \`hv\` (the nonzero proof). \`hv.1\` would be the eigenvector equation.
- \`by ...\` after \`<|\` is a nested tactic block supplying the final proof term.
- \`simpa\` is \`simp\` plus closing the goal; \`using h_sq\` rewrites with the previously proven \`h_sq\`.
- \`[mul_assoc, smul_smul]\` are rewrite lemmas for associativity of multiplication and scalar multiplication.

## Takeaway

The eigenvalues of the Huang matrix are completely determined by its squaring relation:

\`\`\`
A^2 = n I  =>  μ^2 = n.
\`\`\`

So eigenvalues are characterized by the equation \`μ^2 = n\`. This is the standard algebraic pattern: if a matrix squares to a scalar multiple of the identity, every eigenvalue squares to that scalar.

---

*(The comment at the end hints at defining the sorted list of eigenvalues as the sorted roots of the characteristic polynomial, but the proof here focuses only on the equation \`μ^2 = n\`.)*
`;

sectionContent[9] = `# Section 9: Sorted Eigenvalues and Interlacing

This section introduces a few Lean definitions and lemmas that set up a web-style treatment of eigenvalue ordering and the classic interlacing pattern. The code is short, but it lays key groundwork: how to sort eigenvalues, how to express interlacing as a list property, and how symmetry ties to Hermitian structure.

## 1. Sorting eigenvalues from the characteristic polynomial

\`\`\`lean
noncomputable def sorted_eigenvalues_list {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : List ℝ :=
  (A.charpoly.roots).sort (· ≤ ·)
\`\`\`

**Idea.** A matrix has a characteristic polynomial \`A.charpoly\`, whose roots are the eigenvalues (with multiplicity). The definition above collects those roots into a list and then sorts them using the usual order \`≤\` on real numbers.

**Lean syntax notes.**
- \`noncomputable def\` introduces a definition that uses classical (non-constructive) choice. Lean allows it, but it cannot be executed as a program.
- \`{n : ℕ}\` is an implicit argument (Lean will infer it), while \`(A : Matrix (Fin n) (Fin n) ℝ)\` is an explicit argument with type annotation.
- \`:=\` starts the definition body.
- \`List ℝ\` is the list type over real numbers.
- \`(A.charpoly.roots)\` is a list of roots (with multiplicity) of the characteristic polynomial.
- \`.sort (· ≤ ·)\` sorts using the comparator \`≤\`. The notation \`·\` is an anonymous argument placeholder; \`(· ≤ ·)\` is shorthand for \`fun x y => x ≤ y\`.

**Why \`noncomputable\`?** Extracting roots from a polynomial over \`ℝ\` is not computable in Lean's constructive sense. The definition is still valid mathematically, but it must be marked \`noncomputable\`.

**Takeaway.** \`sorted_eigenvalues_list A\` is a sorted list of the eigenvalues of \`A\`, coming directly from the characteristic polynomial.

## 2. Interlacing as a list predicate

\`\`\`lean
/--
A predicate asserting that list M interlaces list L.
-/
def interlacing (L M : List ℝ) : Prop :=
  L.length = M.length + 1 ∧
  ∀ i : Fin M.length, L[i]! ≤ M[i]! ∧ M[i]! ≤ L[i.1 + 1]!
\`\`\`

**Definition.** The predicate says:

- \`L\` has one more element than \`M\`.
- Each element of \`M\` lies between consecutive elements of \`L\`.

Concretely, if \`L = [λ₀, λ₁, ..., λₙ]\` and \`M = [μ₀, ..., μ_{n-1}]\`, then

\`\`\`
λ₀ ≤ μ₀ ≤ λ₁ ≤ μ₁ ≤ ... ≤ λ_{n-1} ≤ μ_{n-1} ≤ λₙ.
\`\`\`

**Lean indexing details.**
- \`L[i]!\` means "the \`i\`-th entry of \`L\`", using \`get!\` (which is safe here because the lengths line up).
- \`i : Fin M.length\` is a finite index guaranteed to be in bounds.
- \`i.1 + 1\` is the successor index in the ambient \`Nat\`.

**Lean syntax notes.**
- \`def interlacing (L M : List ℝ) : Prop :=\` defines a proposition-valued predicate.
- \`∧\` is conjunction, \`∀\` is universal quantification.
- \`Fin M.length\` is the type of natural numbers \`i\` with \`i < M.length\`.
- \`L[i]!\` is the "unsafe" indexer, but it is safe here because \`i\` is a \`Fin\` index.
- \`i.1\` projects the underlying \`Nat\` from a \`Fin\` value.

This is the standard formalization of interlacing for ordered lists.

## 3. Symmetric vs. Hermitian (over \`ℝ\`)

\`\`\`lean
/--
A real matrix is symmetric if and only if it is Hermitian.
-/
theorem isSymm_iff_isHermitian_real {n : Type*} [Fintype n] (A : Matrix n n ℝ) :
  A.IsSymm ↔ A.IsHermitian := by
  rw [Matrix.IsSymm, Matrix.IsHermitian, Matrix.conjTranspose, Matrix.transpose]
  simp
  rfl
\`\`\`

**Idea.** In real matrices, conjugate transpose is just transpose, so "Hermitian" is the same as "symmetric." The proof unfolds definitions and simplifies.

This lemma is crucial because many spectral theorems in mathlib are stated for Hermitian matrices, but we want to apply them to symmetric real matrices.

**Lean syntax notes.**
- \`theorem ... : A.IsSymm ↔ A.IsHermitian := by\` starts a proof; \`by\` introduces tactic mode.
- \`{n : Type*} [Fintype n]\` declares an implicit type and a typeclass instance; \`Fintype\` provides a finite enumeration of \`n\`.
- \`rw [...]\` rewrites the goal using definitional equalities listed in the bracket.
- \`simp\` simplifies using rewriting rules and simp lemmas.
- \`rfl\` closes a goal that is definitionally equal to itself (reflexivity).

## 4. Sorted eigenvalues for symmetric matrices

\`\`\`lean
/--
The sorted eigenvalues of a symmetric matrix.
-/
noncomputable def sorted_eigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) : List ℝ :=
  let hA' : A.IsHermitian := (isSymm_iff_isHermitian_real A).mp hA
  (List.ofFn (hA'.eigenvalues)).mergeSort (· ≤ ·)
\`\`\`

**Idea.** For symmetric (Hermitian) matrices, mathlib gives a function \`eigenvalues\` that returns the eigenvalues as a function \`Fin n → ℝ\`. We convert this function to a list using \`List.ofFn\` and sort with \`mergeSort\`.

- \`hA'\` is the same matrix, but typed as Hermitian.
- \`mergeSort\` produces a sorted list of length \`n\`.

This definition is the "canonical" sorted eigenvalue list for symmetric real matrices.

**Lean syntax notes.**
- \`let hA' : A.IsHermitian := ...\` introduces a local definition with an explicit type.
- \`(isSymm_iff_isHermitian_real A).mp hA\` uses \`.mp\` to take the forward direction of an \`↔\` proof.
- \`List.ofFn\` turns a function \`Fin n → ℝ\` into a list of length \`n\`.
- \`mergeSort\` is a stable sorting function; \`(· ≤ ·)\` is the comparator.

## 5. Length of the sorted eigenvalue list

\`\`\`lean
/--
The number of sorted eigenvalues is n.
-/
theorem sorted_eigenvalues_length {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  (sorted_eigenvalues A hA).length = n := by
    unfold sorted_eigenvalues; aesop;
\`\`\`

**Idea.** The list produced from \`Fin n → ℝ\` has exactly \`n\` entries. After sorting, the length is preserved, so the result remains \`n\`.

The proof uses \`aesop\` to discharge the bookkeeping automatically.

**Lean syntax notes.**
- \`unfold sorted_eigenvalues\` expands the definition so the goal can be simplified.
- \`;\` sequences tactics; here it applies \`aesop\` after \`unfold\` and to any remaining goals.
- \`aesop\` is an automation tactic that solves many routine goals by search.

## 6. Symmetry and the dot product

\`\`\`lean
/--
For a symmetric matrix A, <Ax, y> = <x, Ay>.
-/
theorem dotProduct_mulVec_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (x y : Fin n → ℝ) :
  dotProduct (A.mulVec x) y = dotProduct x (A.mulVec y) := by
    simp +decide [ Matrix.mulVec, dotProduct, mul_comm ];
    simp +decide only [Finset.mul_sum _ _ _, mul_left_comm, mul_comm];
    rw [ Finset.sum_comm ];
    conv_rhs => rw [ ← hA ] ;
    rfl
\`\`\`

**Idea.** Symmetric matrices are self-adjoint, so they can "move" between slots of the dot product. This lemma is a concrete dot-product identity that is frequently used when proving variational characterizations of eigenvalues.

The proof is a sequence of algebraic rewrites: expand the dot product, commute sums, and use the symmetry \`hA\` to swap indices.

**Lean syntax notes.**
- \`simp +decide\` runs the simplifier and also allows \`decide\` to resolve propositional goals.
- \`simp ... only [...]\` restricts simp to the listed lemmas.
- \`rw [Finset.sum_comm]\` rewrites using commutativity of finite sums.
- \`conv_rhs => ...\` opens a "conversion" block to rewrite just the right-hand side.
- \`rw [← hA]\` uses the symmetry proof to replace \`A\` with its transpose.
- \`rfl\` finishes once both sides are definitionally equal.

## 7. Where this is headed

The file ends with a comment marker:

\`\`\`lean
/--
The max-min value for the k-th eigenvalue.
-/
\`\`\`

This indicates the next step: a max-min (or min-max) characterization of eigenvalues (the Courant--Fischer theorem). With the definitions here, one can state and prove interlacing results for eigenvalues of principal submatrices or rank-one updates.

## Summary

- \`sorted_eigenvalues_list\` sorts roots of the characteristic polynomial.
- \`interlacing\` formalizes the classic eigenvalue interlacing pattern.
- \`isSymm_iff_isHermitian_real\` bridges symmetric and Hermitian worlds.
- \`sorted_eigenvalues\` extracts eigenvalues of symmetric matrices and sorts them.
- \`sorted_eigenvalues_length\` and \`dotProduct_mulVec_symm\` are foundational lemmas for variational principles.

These pieces form the Lean infrastructure for talking about ordered eigenvalues and their interlacing behavior.
`;

sectionContent[10] = `# Section 10: Min–Max Eigenvalues and Spectral Theory (Lean Walkthrough)

This section defines the min–max eigenvalue of a real symmetric matrix and proves two key spectral facts:

- the list of sorted eigenvalues is just a permutation of the (unsorted) eigenvalues, and
- there is an orthonormal eigenbasis aligned with the sorted eigenvalues.

We also record that the Euclidean inner product is the same as \`dotProduct\` in Lean.

Throughout, \`A : Matrix (Fin n) (Fin n) ℝ\` is a real matrix and \`hA : A.IsSymm\` means \`A\` is symmetric.

---

## 1. The min–max eigenvalue (Rayleigh–Ritz form)

Lean definition:

\`\`\`lean
def min_max_eigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ⨆ (C : Submodule ℝ (Fin n → ℝ)) (_ : Module.finrank ℝ C = k + 1),
    ⨅ (x : {x : C // dotProduct (x : Fin n → ℝ) (x : Fin n → ℝ) = 1}),
      dotProduct (A.mulVec (x : Fin n → ℝ)) (x : Fin n → ℝ)
\`\`\`

**What this means** (mathematically):

- You look at all subspaces \`C\` of dimension \`k+1\`.
- In each subspace, you take the **minimum** of the Rayleigh quotient over unit vectors \`x\` in \`C\`.
- Then you take the **maximum** of those minima over all such subspaces.

This is the classical min–max characterization of the \`k\`-th eigenvalue for symmetric matrices.

Key Lean ideas:

- \`⨆\` and \`⨅\` are \`iSup\` and \`iInf\`, the supremum and infimum operators.
- \`Module.finrank ℝ C = k + 1\` enforces the subspace dimension.
- The unit sphere in \`C\` is encoded as a subtype
  \`x : {x : C // dotProduct x x = 1}\`.
- The Rayleigh quotient is just \`dotProduct (A.mulVec x) x\` for real symmetric matrices.
- \`def\` introduces a definition; \`:=\` provides its value.
- \`{n : ℕ}\` is an implicit parameter; \`:\` separates a name from its type.
- \`C : Submodule ℝ (Fin n → ℝ)\` binds a submodule of functions \`Fin n → ℝ\`.
- \`(_ : Module.finrank ℝ C = k + 1)\` is an anonymous binder that supplies a proof of the dimension constraint.
- \`x : {x : C // ...}\` is a subtype; \`x\` carries both a vector and a proof it has unit norm.
- Coercions like \`(x : Fin n → ℝ)\` turn \`x\` from a submodule element into the underlying function.
- \`A.mulVec\` is matrix–vector multiplication; \`•\` is scalar multiplication.

---

## 2. Sorted eigenvalues are a permutation of eigenvalues

Lemma (paraphrased):

> The list \`sorted_eigenvalues A hA\` is a permutation of the standard eigenvalue list of \`A\`.

Lean statement:

\`\`\`lean
lemma sorted_eigenvalues_is_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  ∃ σ : Equiv.Perm (Fin n), ∀ (i : Fin n),
    (sorted_eigenvalues A hA).get ⟨i, ...⟩ =
    Matrix.IsHermitian.eigenvalues ((isSymm_iff_isHermitian_real A).mp hA) (σ i)
\`\`\`

Lean syntax notes:

- \`lemma\` starts a named proposition; it is definitionally the same as \`theorem\`.
- \`∃ σ : Equiv.Perm (Fin n),\` is an existence statement for a permutation of \`Fin n\`.
- \`∀ (i : Fin n)\` is a universal quantifier; \`Fin n\` is the finite type of indices.
- \`(sorted_eigenvalues A hA).get ⟨i, ...⟩\` uses \`List.get\`, which requires a proof that \`i\` is in bounds; \`⟨i, ...⟩\` is a \`Subtype\` value with the omitted proof represented by \`...\`.
- \`Matrix.IsHermitian.eigenvalues\` is the standard eigenvalue list for a Hermitian matrix.
- \`(isSymm_iff_isHermitian_real A).mp hA\` converts a real symmetry proof into a Hermitian proof; \`.mp\` is the forward direction of an \`Iff\`.
- \`(σ i)\` applies the permutation to the index.

**Proof idea**:

1. \`sorted_eigenvalues\` is defined as a merge sort of the eigenvalues list, so it is a permutation.
2. A generic lemma shows: if two lists are permutations, then there is a bijection between their indices that matches entries.
3. That bijection is transported to a permutation of \`Fin n\` using length equalities.

**Why this matters**:

This gives a precise index map \`σ\` so you can connect the *sorted* eigenvalue list to the *original* eigenvalue list. It is a technical bridge for reindexing eigenvectors.

---

## 3. Orthonormal basis aligned to the sorted eigenvalues

Lemma (paraphrased):

> There is an orthonormal basis \`v\` of eigenvectors such that the eigenvalue of \`v i\` is exactly the \`i\`-th sorted eigenvalue.

Lean statement:

\`\`\`lean
lemma exists_orthonormal_basis_sorted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  ∃ (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))),
    ∀ i, A.mulVec (v i) =
      ((sorted_eigenvalues A hA).get ⟨i, ...⟩) • (v i)
\`\`\`

Lean syntax notes:

- \`∃ (v : OrthonormalBasis ...)\` quantifies an orthonormal basis as a dependent object.
- \`v i\` is the basis vector at index \`i\`; \`A.mulVec (v i)\` is the matrix acting on that vector.
- \`•\` is scalar multiplication in the vector space \`EuclideanSpace ℝ (Fin n)\`.
- \`v.reindex σ.symm\` (used in the proof) reorders the basis by a permutation; \`.symm\` is the inverse permutation.

**Proof idea**:

1. The spectral theorem already provides an orthonormal eigenbasis indexed by the *unsorted* eigenvalues.
2. Using the permutation \`σ\` from the previous lemma, reindex that basis so the \`i\`-th basis vector corresponds to the \`i\`-th sorted eigenvalue.
3. The lemma uses \`v.reindex σ.symm\` to align the ordering.

**Takeaway**:

For symmetric matrices, not only do eigenvalues exist and are real, but you can order them and still have an orthonormal basis of eigenvectors in that order.

---

## 4. Inner product equals dot product

Lean lemma:

\`\`\`lean
lemma inner_eq_dotProduct {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
  inner ℝ x y = dotProduct (x : Fin n → ℝ) (y : Fin n → ℝ) := by
    simp +decide [ dotProduct, inner ];
    ac_rfl
\`\`\`

Lean tactic notes:

- \`:= by\` starts a tactic proof.
- \`simp\` simplifies the goal using rewriting rules; \`+decide\` lets \`simp\` discharge decidable propositions automatically.
- \`[ dotProduct, inner ]\` tells \`simp\` to unfold these definitions during simplification.
- \`ac_rfl\` finishes goals that are true by associativity/commutativity of addition and multiplication.

This is a small but important bridge: \`EuclideanSpace\` in mathlib is defined using the dot product on functions \`Fin n → ℝ\`. The lemma tells Lean (and the reader) that the abstract inner product agrees with the concrete dot product formula.

---

## How these pieces fit together

- The **min–max eigenvalue** definition uses the Rayleigh quotient, which relies on the **dot product**.
- The **permutation lemma** formalizes that sorted eigenvalues are just a reordering of the standard list.
- The **orthonormal basis lemma** uses that permutation to reorder eigenvectors so each basis vector matches the sorted eigenvalue at the same index.

Altogether, this section is a Lean formalization of the spectral theorem framework needed for min–max eigenvalue proofs.
`;

sectionContent[11] = `# Section 11: g-Transform Expectation is Nonzero

This section explains the Lean theorem \`g_expectation_nonzero\`, which shows that a specific sum (an expectation-like quantity) is nonzero when a Boolean function has full degree. The statement connects the top Fourier coefficient of a Boolean function to the nonvanishing of a signed sum involving the parity character.

## The Lean statement

\`\`\`lean
theorem g_expectation_nonzero {n : ℕ} (f : (Fin n → Bool) → Bool)
  (h_deg : degree f = n) (hn : n ≠ 0) :
  let g := fun x => (if f x then 1 else 0) * chi Finset.univ x
  (Finset.sum Finset.univ g) ≠ 0 := by
  ...
\`\`\`

### Lean syntax and constructs in the statement

Below is a quick guide to the Lean keywords, binders, and notation used in the statement.

- \`theorem g_expectation_nonzero\`: declares a theorem with the given name.
- \`{n : ℕ}\`: an implicit argument (Lean will try to infer it). \`ℕ\` is the type of natural numbers.
- \`(f : (Fin n → Bool) → Bool)\`: an explicit argument. Here \`Fin n\` is the finite type with \`n\` elements (indices \`0\` to \`n-1\`), so \`Fin n → Bool\` is a length‑\`n\` Boolean input.
- \`(h_deg : degree f = n) (hn : n ≠ 0)\`: hypotheses with names. \`≠\` is “not equal.”
- \`:\` separates the hypotheses from the goal statement.
- \`let g := ...\`: local definition used in the goal. \`g\` is defined only for the remainder of the statement.
- \`fun x => ...\`: lambda (anonymous function) definition.
- \`if f x then 1 else 0\`: Boolean-to-number coercion via a conditional expression (gives \`1\` when \`f x\` is true, else \`0\`).
- \`*\`: multiplication in the codomain (\`ℝ\` here).
- \`chi Finset.univ x\`: the parity character \`χ_S\` evaluated at \`x\`, with \`S = Finset.univ\`.
- \`Finset.univ\`: the finite set containing all elements of a finite type.
- \`Finset.sum Finset.univ g\`: sum of \`g x\` over all \`x\` in the finite set; this is the discrete expectation without normalization.
- \`≠ 0\`: the conclusion that the sum is not zero.
- \`:= by ...\`: begins a tactic proof. Everything after \`by\` is a sequence of tactics that transform the goal until it is solved.

### What it means in plain language

- We have a Boolean function \\(f : \\{0,1\\}^n \\to \\{0,1\\}\\).
- The **Fourier degree** of \\(f\\) is \\(n\\), i.e., the largest \\(|S|\\) with \\(\\hat{f}(S) \\neq 0\\) equals \\(n\\).
- We define a transform \\(g : \\{0,1\\}^n \\to \\mathbb{R}\\) by:
\\[
g(x) = \\mathbf{1}_{f(x)=\\text{true}} \\cdot \\chi_{[n]}(x)
\\]
where \\(\\mathbf{1}_{f(x)=\\text{true}}\\) is 1 if \\(f(x)\\) is true, 0 otherwise, and \\(\\chi_{[n]}(x)\\) is the full parity character (defined in **Section 3**).
- The theorem says \\(\\sum_{x \\in \\{0,1\\}^n} g(x) \\neq 0\\).

**Codomain note**: The expression \`(if f x then 1 else 0) * chi Finset.univ x\` has type \`ℝ\` in Lean, since \`chi\` returns a real number (\\(\\pm 1\\)) and the multiplication is in \\(\\mathbb{R}\\).

This sum is (up to normalization) the Fourier coefficient at the full set \\(S = [n]\\). If the degree is \\(n\\), then this top coefficient is nonzero, so the sum cannot vanish.

## Intuition: why the sum is the Fourier coefficient

For a Boolean function, the Fourier coefficient at a set \\(S\\) is:
\\[
\\hat{f}(S) = \\frac{1}{2^n} \\sum_{x \\in \\{0,1\\}^n} f(x) \\cdot \\chi_S(x)
\\]

The Lean definition uses this same formula (see **Section 4**). The key observation is:
\\[
\\sum_x g(x) = \\sum_x f(x) \\cdot \\chi_{[n]}(x) = 2^n \\cdot \\hat{f}([n])
\\]

So the sum equals \\(2^n\\) times the Fourier coefficient at the full set. Since \\(2^n \\neq 0\\), the sum is nonzero if and only if \\(\\hat{f}([n]) \\neq 0\\).

In the theorem:

- \`S\` is the full set \`Finset.univ\`.
- \`f(x)\` is represented as \`(if f x then 1 else 0)\` to move from \`Bool\` to \`Nat\` (or \`Int\`).
- \`chi Finset.univ x\` is the parity character on all \`n\` bits.

So the sum

\`\`\`
Finset.sum Finset.univ (fun x => (if f x then 1 else 0) * chi Finset.univ x)
\`\`\`

is exactly the (unnormalized) Fourier coefficient at the full set. If the degree is \`n\`, then the top coefficient is nonzero, and therefore the sum cannot be zero.

## How the Lean proof works

The proof is structured in three logical steps:

1. **Extract a nonzero top coefficient.**
   It proves there exists a set \`S\` of size \`n\` such that \`fourier_coeff f S ≠ 0\`. This uses the assumption \`degree f = n\` and a contradiction argument: if all size-\`n\` coefficients were zero, the degree would be at most \`n-1\`.

2. **Specialize to the full set.**
   For \`Fin n\`, the only subset of size \\(n\\) is \`Finset.univ\`. The argument is:
   - We have \\(S \\subseteq \\text{Finset.univ}\\) (any finset over \`Fin n\`)
   - We have \\(|S| = n\\)
   - But \\(|\\text{Finset.univ}| = n\\) (since \`Fintype.card (Fin n) = n\`)
   - A subset of a finite set with equal cardinality must be the whole set

   Lean uses \`Finset.eq_of_subset_of_card_le\` to conclude \\(S = \\text{Finset.univ}\\).

3. **Rewrite the coefficient as a sum.**
   After simplification, the coefficient is shown to be exactly the sum of \`g(x)\` over all \`x\`. Since the coefficient is nonzero, the sum is nonzero.

In Lean, those steps appear as:

\`\`\`lean
have h_fourier_coeff : ∃ S : Finset (Fin n), fourier_coeff f S ≠ 0 ∧ S.card = n := by
  ...
obtain ⟨ S, hS₁, hS₂ ⟩ := h_fourier_coeff
simp_all +decide [ fourier_coeff ]
have := Finset.eq_of_subset_of_card_le ( Finset.subset_univ S )
...
\`\`\`

The proof uses \`simp_all\` to unfold \`fourier_coeff\` and reduce to the explicit sum, and \`Finset.eq_of_subset_of_card_le\` to pin down \`S = Finset.univ\` from the cardinality equation.

### Lean tactics and proof keywords used above

- \`have h_fourier_coeff : ... := by\`: introduces an intermediate lemma with a proof block. The type after \`:\` is the statement being proved.
- \`∃ S : Finset (Fin n), ...\`: an existential statement (“there exists a finite set \`S\` …”). \`Finset (Fin n)\` is a finite set of indices from \`Fin n\`.
- \`∧\`: conjunction (“and”), so the witness \`S\` must satisfy both properties.
- \`S.card = n\`: the cardinality (size) of the finite set \`S\` is \`n\`.
- \`obtain ⟨ S, hS₁, hS₂ ⟩ := h_fourier_coeff\`: destructs the existential proof, binding the witness \`S\` and its two properties to names \`hS₁\` and \`hS₂\`.
- \`simp_all\`: a simplification tactic that uses all available hypotheses and simp lemmas to reduce the goal. It performs rewriting, unfolding, and canonical simplifications.
- \`+decide\`: adds \`decide\`-based simp lemmas, allowing \`simp_all\` to solve or simplify goals that depend on decidable propositions (e.g., finite set membership).
- \`[ fourier_coeff ]\`: tells \`simp_all\` to unfold the definition \`fourier_coeff\`.
- \`have := ...\`: introduces a new fact with an inferred name (Lean creates a fresh identifier). Often used when the exact name is not important.
- \`Finset.eq_of_subset_of_card_le\`: lemma stating that if \`A ⊆ B\` and \`card B ≤ card A\`, then \`A = B\`. Here it shows \`S = Finset.univ\`.
- \`Finset.subset_univ S\`: proof that any finite set \`S\` is a subset of the universal finite set.

## Takeaway

If a Boolean function has full Fourier degree, then its correlation with the full parity character is nonzero. The \`g\`-transform expectation encodes that correlation, so the sum (expectation) cannot vanish. This is a compact way to say: **full degree implies a nonzero top Fourier coefficient, which forces a nonzero global parity sum.**
`;

sectionContent[12] = `# Section 12: Reindexed Huang Matrix and Symmetry

This section introduces a convenient reindexing of the Huang matrix so that its rows and columns are indexed by \`Fin (2^n)\` instead of boolean functions \`Fin n -> Bool\`. It then proves that both the original and reindexed Huang matrices are symmetric. The main ideas are:

- Build an explicit equivalence between boolean functions and \`Fin (2^n)\`.
- Use \`Matrix.reindex\` to transport the Huang matrix across that equivalence.
- Prove symmetry for the original matrix by induction on \`n\`.
- Conclude symmetry for the reindexed matrix by rewriting via the equivalence.

## 1. Reindexing boolean functions to \`Fin (2^n)\`

\`\`\`lean
def boolFunEquivFin (n : ℕ) : (Fin n → Bool) ≃ Fin (2^n) :=
  (Fintype.equivFin (Fin n → Bool)).trans (finCongr (by
  norm_num [ Fintype.card_pi ]))
\`\`\`

**What this does:**
- \`Fintype.equivFin\` produces an equivalence between any finite type and \`Fin (card _)\`.
- \`Fin n -> Bool\` has cardinality \`2^n\`. The proof uses \`Fintype.card_pi\` and \`norm_num\` to simplify the count.
- \`finCongr\` adjusts the \`Fin\` index to exactly \`Fin (2^n)\`.

So \`boolFunEquivFin n\` is the canonical bridge between boolean functions on \`n\` bits and the \`2^n\` sized \`Fin\` type.

**Lean syntax and tactic details:**
- \`def\` introduces a new definition; the name \`boolFunEquivFin\` is the constant being defined.
- \`(n : ℕ)\` is a typed parameter; \`ℕ\` is the natural numbers.
- \`: (Fin n → Bool) ≃ Fin (2^n)\` is the type annotation, saying this is an equivalence (\`≃\`) between two types.
- \`:=\` starts the definition body.
- \`(Fintype.equivFin (Fin n → Bool))\` is a term that builds an equivalence from a finite type to \`Fin (card _)\`.
- \`.trans\` composes equivalences: \`e.trans f\` is the equivalence obtained by first applying \`e\`, then \`f\`.
- \`finCongr\` changes the \`Fin\` index using a proof that the sizes are equal.
- \`by ...\` starts a tactic proof block.
- \`norm_num\` is a simplification tactic for arithmetic/numeral goals; here it reduces the cardinality formula.
- \`[ Fintype.card_pi ]\` is a simp-lemma list telling \`norm_num\` which lemma to use; \`Fintype.card_pi\` computes the cardinality of a function type.

## 2. The reindexed Huang matrix

\`\`\`lean
noncomputable def huang_matrix_fin (n : ℕ) : Matrix (Fin (2^n)) (Fin (2^n)) ℝ :=
  Matrix.reindex (boolFunEquivFin n) (boolFunEquivFin n) (huang_matrix n)
\`\`\`

\`Matrix.reindex\` transports a matrix along equivalences of row and column indices. Here we use the same equivalence for rows and columns, so we are simply relabeling the indices, not changing any numeric entries.

This gives a version of the Huang matrix whose index type matches the usual \`2^n x 2^n\` dimension found in linear algebra statements.

**Lean syntax and tactic details:**
- \`noncomputable\` marks the definition as potentially noncomputable (e.g., it uses choice); Lean will not demand computational content.
- \`Matrix (Fin (2^n)) (Fin (2^n)) ℝ\` is a matrix with row and column index types \`Fin (2^n)\` over the reals \`ℝ\`.
- \`Matrix.reindex\` takes two equivalences (for rows and columns) and a matrix, and returns the relabeled matrix.
- \`huang_matrix n\` is the original Huang matrix, with indices in \`Fin n → Bool\`.

## 3. The original Huang matrix is symmetric

\`\`\`lean
theorem huang_matrix_isSymm (n : ℕ) : (huang_matrix n).IsSymm := by
  induction' n with n ih;
  · exact rfl
  · -- By definition of huang_matrix, we know that huang_matrix (n + 1) is a block matrix ...
    have h_block : huang_matrix (n + 1) = Matrix.reindex (finSuccEquiv_huang_custom n).symm
      (finSuccEquiv_huang_custom n).symm
      (Matrix.fromBlocks (huang_matrix n) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ)
        (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (-huang_matrix n)) := by
      rfl;
    simp_all +decide [ Matrix.IsSymm ];
    ext i j; simp +decide [ Matrix.fromBlocks_transpose, ih ] ;
\`\`\`

**Key idea:** the matrix for \`n+1\` is built as a block matrix (with \`huang_matrix n\` and \`-huang_matrix n\` on the diagonal, and identities off-diagonal), then reindexed to match the boolean hypercube structure. The proof:

- Proceeds by induction on \`n\`.
- For \`n = 0\`, symmetry is \`rfl\`.
- For \`n + 1\`, it unfolds the block structure and uses the inductive hypothesis that \`huang_matrix n\` is symmetric.
- \`simp\` with \`Matrix.fromBlocks_transpose\` shows the block matrix is symmetric.

This is the structural heart of the symmetry result.

**Lean syntax and tactic details:**
- \`theorem\` introduces a named proposition with a proof.
- \`: (huang_matrix n).IsSymm\` is the goal type; \`IsSymm\` is a predicate on matrices.
- \`by\` starts a tactic proof.
- \`induction' n with n ih;\` performs induction on \`n\`, naming the predecessor \`n\` and induction hypothesis \`ih\`. The prime \`'\` is the version that supports naming binders.
- \`·\` starts a bullet for a proof branch (base case, then inductive case).
- \`exact rfl\` closes the goal by reflexivity; \`rfl\` proves definitional equalities.
- \`have h_block : ... := by rfl\` introduces a local lemma; the \`: ...\` annotates the lemma’s type, and \`rfl\` proves it by unfolding the definition.
- \`Matrix.reindex\` and \`.symm\` reindex with the inverse equivalence (\`symm\` flips direction).
- \`Matrix.fromBlocks\` builds a block matrix from four submatrices.
- \`1 : Matrix ...\` is the identity matrix on the relevant index type; the type annotation guides elaboration.
- \`-huang_matrix n\` is the pointwise negation of the matrix.
- \`simp_all\` simplifies all goals and hypotheses; \`+decide\` tells \`simp\` to use decision procedures for \`Decidable\` propositions.
- \`[ Matrix.IsSymm ]\` supplies the simp lemma characterizing symmetry via transpose.
- \`ext i j\` applies the extensionality lemma for matrices, reducing the goal to entrywise equality.
- \`simp\` then closes the entrywise goal, using \`Matrix.fromBlocks_transpose\` and the inductive hypothesis \`ih\`.

## 4. Symmetry survives reindexing

\`\`\`lean
theorem huang_matrix_fin_isSymm (n : ℕ) : (huang_matrix_fin n).IsSymm := by
  exact funext fun i => funext fun j => huang_matrix_isSymm n |>.apply _ _
\`\`\`

A reindexing does not change the entries, only the labels. The proof simply reduces symmetry of the reindexed matrix to symmetry of the original by expanding definitions.

In other words, symmetry is invariant under relabeling of indices by equivalence.

**Lean syntax and tactic details:**
- \`funext\` is function extensionality: to show two functions are equal, it suffices to show they agree on every input.
- \`fun i => ...\` introduces a lambda; \`funext fun i => ...\` is the extensionality proof for the first index, then again for the second.
- \`huang_matrix_isSymm n |>.apply _ _\` uses function application in forward-pipe style (\`|>\`). \`IsSymm\` is a function that, when applied, yields the entrywise symmetry proof; underscores \`_\` are placeholders for inferred indices.
- \`exact\` supplies the constructed proof term directly.

## 5. Takeaway

- \`boolFunEquivFin\` is the bridge from boolean function indices to \`Fin (2^n)\`.
- \`huang_matrix_fin\` is a pure reindexing, so algebraic properties such as symmetry carry over immediately.
- The core symmetry proof relies on the block decomposition of the Huang matrix and an induction on dimension.

If you want to connect this to linear algebra over finite-dimensional real vector spaces, \`huang_matrix_fin\` is the version with the standard \`2^n x 2^n\` index type, and \`huang_matrix_fin_isSymm\` confirms it is symmetric in the usual sense.
`;

sectionContent[13] = `# Section 13: Complete Spectrum of the Huang Matrix

This section proves the full list of eigenvalues of the Huang matrix (in the \`Fin\`-indexed form) and shows that they are exactly half negative and half positive square roots.

We will walk through the proof structure and explain the key lemmas.

## Goal: the complete spectrum

For the Huang matrix on dimension \`n+1\` (size \`2^(n+1)\`), the theorem proved is:

- The sorted eigenvalues are:

\`\`\`
[-sqrt(n+1), ..., -sqrt(n+1)]  (2^n times)
[+sqrt(n+1), ..., +sqrt(n+1)]  (2^n times)
\`\`\`

In other words, the spectrum is exactly two values, \`-sqrt(n+1)\` and \`+sqrt(n+1)\`, each with multiplicity \`2^n\`.

In Lean, this appears as:

\`\`\`lean
lemma huang_eigenvalues_eq_list_succ (n : ℕ) :
  let evs := sorted_eigenvalues (huang_matrix_fin (n + 1)) (huang_matrix_fin_isSymm (n + 1))
  evs = List.replicate (2^n) (-Real.sqrt (n + 1)) ++
        List.replicate (2^n) (Real.sqrt (n + 1))
\`\`\`

Lean syntax notes:

- \`lemma ... :\` introduces a named theorem with its statement (type).
- \`(n : ℕ)\` declares \`n\` as a natural number; \`ℕ\` is the type of naturals.
- \`let evs := ...\` is a local definition scoped to the statement.
- \`sorted_eigenvalues A hA\` expects a matrix \`A\` and a proof \`hA\` that \`A\` is symmetric.
- \`huang_matrix_fin (n + 1)\` is the \`Fin\`-indexed Huang matrix at dimension \`n+1\`.
- \`huang_matrix_fin_isSymm (n + 1)\` supplies the symmetry proof for that matrix.
- \`List.replicate k x\` is the list of length \`k\` filled with \`x\`.
- \`++\` concatenates lists.
- \`Real.sqrt\` is the real square root function; \`-Real.sqrt (n + 1)\` is unary negation.

The rest of the section is a chain of lemmas that make this statement inevitable.

## Step 1: Every eigenvalue squares to \`n\`

The theorem \`huang_eigenvalues_sq_eq_n\` shows that for the \`Fin\`-indexed Huang matrix, *every eigenvalue* satisfies

\`\`\`
mu^2 = n
\`\`\`

Sketch of the proof:

1. Use the matrix identity \`A^2 = n * I\` (proved earlier as \`huang_matrix_fin_sq\`).
2. If \`A v = mu v\`, then apply \`A\` again to get \`A (A v) = mu^2 v\`.
3. Replace \`A^2\` with \`n I\` to get \`n v\` on the left, so \`mu^2 v = n v\`.
4. Since \`v != 0\`, conclude \`mu^2 = n\`.

This lemma is then applied to every element of \`sorted_eigenvalues\` to state that *every entry in the list squares to \`n\`*.

Lean syntax notes (common constructs in this step):

- \`A v = mu v\` is an equation in the \`Matrix\`/\`LinearMap\` setting, using multiplication notation.
- \`A^2\` is \`A\` squared; the \`^\` notation uses \`Pow.pow\` for the matrix type.
- \`n * I\` is scalar multiplication of the identity matrix \`I\`.
- Proofs here typically use rewriting (\`rw\`), simplification (\`simp\`), and nonzero arguments (\`by_contra\`, \`by_cases\`).

## Step 2: Sum of eigenvalues equals trace

\`sum_sorted_eigenvalues_eq_trace\` proves that for a symmetric real matrix, the sum of the sorted eigenvalues equals the trace:

\`\`\`
(sorted_eigenvalues A hA).sum = A.trace
\`\`\`

This uses the standard fact that the trace of a symmetric matrix is the sum of its (real) eigenvalues, and shows that sorting does not change the sum.

Lean syntax notes:

- \`(sorted_eigenvalues A hA).sum\` uses \`List.sum\` via dot notation to add list entries.
- \`A.trace\` is \`Matrix.trace A\`, written with dot notation.
- Equality of sums under sorting usually comes from permutation lemmas (\`List.Perm\`) and \`List.sum_perm\`.

## Step 3: The Huang matrix has trace 0

\`huang_matrix_fin_trace\` uses reindexing to transfer the earlier result that the Huang matrix has trace 0:

\`\`\`
Matrix.trace (huang_matrix_fin n) = 0
\`\`\`

This gives the sum of all eigenvalues immediately:

\`\`\`
(sum of eigenvalues) = 0
\`\`\`

Lean syntax notes:

- \`Matrix.trace\` is defined as the sum of diagonal entries.
- Reindexing often uses \`Equiv\` or \`Fin\`-based equivalences; in Lean these show up as \`Equiv\` values and \`by simpa\` with trace lemmas.

## Step 4: A list lemma for values that square to \`c^2\`

Several list lemmas are introduced to characterize a list that:

- has length \`2m\`,
- all elements satisfy \`x^2 = c^2\`,
- and the sum is 0,
- and the list is sorted.

The key lemma is:

\`\`\`lean
sorted_list_of_sq_eq_and_sum_zero
\`\`\`

Lean syntax notes:

- Names like \`sorted_list_of_sq_eq_and_sum_zero\` package all assumptions (sorted, squares equal, sum zero) into one lemma.
- \`List.Sorted\` and \`List.length\` are standard list predicates used in the proof.
- The step \`x^2 = c^2\` implies \`x = c ∨ x = -c\` uses lemmas like \`mul_self_eq_mul_self_iff\` or \`sq_eq_sq_iff_eq_or_eq_neg\`.

It concludes:

\`\`\`
L = List.replicate m (-c) ++ List.replicate m c
\`\`\`

The logic is simple:

- If \`x^2 = c^2\`, then \`x = c\` or \`x = -c\`.
- If the sum is 0 and \`c != 0\`, then there must be the same number of \`c\` and \`-c\`.
- Sorting forces all \`-c\` values to appear first.

This lemma is the engine behind the final spectral statement.

## Step 5: Apply to \`n+1\`

With the ingredients in place, the final proof is short:

- The list \`sorted_eigenvalues\` has length \`2^(n+1)\`.
- Every entry squares to \`n+1\` (Step 1).
- The sum of the list is 0 (Steps 2 and 3).
- The list is sorted (by construction).

Therefore the list is exactly \`2^n\` copies of \`-sqrt(n+1)\` followed by \`2^n\` copies of \`+sqrt(n+1)\`.

This is the **complete spectrum** of the Huang matrix in the \`Fin\`-indexed model.

Lean syntax notes:

- \`2^n\` is exponentiation in \`ℕ\` and is coerced when used as a list length or as a real number.
- Type coercions from \`Nat\` to \`Real\` are inserted by instances; you may see \`Nat.cast\` in explicit proofs.
- Tactics like \`simp\` and \`linarith\` typically discharge algebraic and linear arithmetic goals in these steps.

## Takeaway

The section combines three classic facts:

1. \`A^2 = n I\` forces eigenvalues to satisfy \`mu^2 = n\`.
2. Trace equals sum of eigenvalues.
3. Sorting plus a zero sum forces exact multiplicities.

As a result, the Huang matrix has only two eigenvalues, \`-sqrt(n)\` and \`+sqrt(n)\`, with equal multiplicity.
`;

sectionContent[14] = `# Section 14: Adjacency and Row-Sum Bounds

This section has two themes:

1. The Huang matrix has entries whose **absolute values** match the adjacency matrix of the hypercube.
2. Any eigenvalue of a real matrix is bounded in absolute value by the **maximum absolute row sum**.

We'll walk through both statements and how the Lean proofs are structured.

---

## 1. Absolute values give the hypercube adjacency

### Statement

\`\`\`lean
theorem abs_huang_eq_adjacency (n : ℕ) (i j : Fin n → Bool) :
  |huang_matrix n i j| =
    if (Finset.filter (fun k => i k ≠ j k) Finset.univ).card = 1
    then 1 else 0 := by
  ...
\`\`\`

Interpretation:

- The vertices of the \`n\`-dimensional hypercube are functions \`Fin n → Bool\`.
- Two vertices \`i\` and \`j\` are adjacent exactly when they differ in **one** coordinate.
- The proof shows that the absolute value of the Huang matrix entry is \`1\` precisely in that case, and \`0\` otherwise.

So \`|huang_matrix n|\` is the adjacency matrix of the hypercube.

Lean syntax notes for the statement above:

- \`theorem\` introduces a named proposition with a proof. Here the name is \`abs_huang_eq_adjacency\`.
- \`(n : ℕ)\` declares a natural number argument; \`ℕ\` is the type of natural numbers.
- \`(i j : Fin n → Bool)\` declares two functions from \`Fin n\` (the finite type \`{0, …, n-1}\`) to \`Bool\`.
- \`|...|\` is the absolute value notation (uses \`abs\` on \`ℝ\` or \`ℤ\`, depending on the matrix entry type).
- \`if ... then ... else ...\` is the standard conditional expression in Lean.
- \`Finset.filter\` keeps elements satisfying the predicate; \`fun k => i k ≠ j k\` is a lambda function.
- \`Finset.univ\` is the finset of all elements of a finite type; here it is all \`k : Fin n\`.
- \`.card\` is the cardinality of a finset.
- \`:= by\` starts a proof block in tactic mode (the proof is filled in by Lean tactics).

### Proof idea

The proof is by induction on \`n\`. There are two main ingredients:

1. **Base case (\`n = 0\`)**: There is only one vertex. The proof is done by case analysis on the only possible indices.
2. **Inductive step**: The Huang matrix for size \`n+2\` is defined in a block form
   \`\`\`lean
   [  A   1
      1  -A ]
   \`\`\`
   after reindexing. This induces a split into two cases based on whether the first coordinates agree:
   - If \`i 0 = j 0\`, the entry reduces to the corresponding entry of the smaller Huang matrix.
   - If \`i 0 ≠ j 0\`, the entry comes from a \`1\` block, but only when the remaining coordinates are identical.

The proof formalizes this with a split lemma \`h_split\` that matches this block structure.
Then it rewrites the "differ in exactly one coordinate" condition to separate the first coordinate from the rest. The cardinality calculation is then handled by \`simp\` and \`Finset.card\` lemmas.

Lean tactic notes for this proof sketch:

- \`simp\` is the simplifier: it rewrites using definitional equalities and lemmas tagged \`[simp]\`.
- \`cases\` or \`cases\`-style case splits (often used for the \`n = 0\` base case) enumerate constructors of a type.
- \`simp [h_split]\` means "simplify, also using the lemma \`h_split\` as a rewrite rule."
- \`Finset.card\` lemmas relate cardinality to \`filter\` and to singleton/empty finsets; these are often triggered by \`simp\`.

---

## 2. Eigenvalues bounded by max absolute row sum

### Statement

\`\`\`lean
theorem eigenvalue_le_max_row_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
  (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
  ∃ i : Fin n, |μ| ≤ Finset.sum Finset.univ (fun j => |A i j|) := by
  ...
\`\`\`

Interpretation:

- If \`μ\` is an eigenvalue of \`A\`, then there exists a row \`i\` whose absolute row sum bounds \`|μ|\`.
- This is a standard norm estimate: the spectral radius is bounded by the max row sum norm.

Lean syntax notes for the statement above:

- \`{n : ℕ}\` uses implicit arguments; Lean can infer \`n\` from context.
- \`Matrix (Fin n) (Fin n) ℝ\` is an \`n × n\` real matrix indexed by \`Fin n\`.
- \`μ : ℝ\` declares a real number.
- \`Module.End.HasEigenvalue (Matrix.toLin' A) μ\` states that the linear map corresponding to \`A\` has eigenvalue \`μ\`.
- \`Matrix.toLin'\` coerces a matrix into a linear map on \`Fin n → ℝ\`.
- \`∃ i : Fin n, ...\` is an existential quantifier: there exists an index \`i\`.
- \`Finset.sum Finset.univ (fun j => |A i j|)\` is the finite sum of absolute values in row \`i\`.
- \`by\` again begins a tactic proof.

### Proof idea

The proof follows the textbook argument:

1. **Pick an eigenvector** \`v\` with \`A.mulVec v = μ • v\`.
2. **Choose an index** \`i\` where \`|v i|\` is maximal (this is done via \`Finset.exists_max_image\`).
3. **Compare absolute values**:
   \`\`\`lean
   |μ * v i| = |(A.mulVec v) i| = |∑ j, A i j * v j|
   ≤ ∑ j, |A i j| * |v j|
   ≤ ∑ j, |A i j| * |v i|
   \`\`\`
4. If \`|v i| = 0\`, then \`v = 0\`, which contradicts the eigenvector being nonzero. So we can divide by \`|v i|\` and obtain the desired bound on \`|μ|\`.

In Lean, the proof is structured around these steps:

- \`obtain ⟨v, hv⟩\` extracts a nonzero eigenvector.
- \`obtain ⟨i, hi⟩\` chooses the maximal coordinate.
- \`h_bound\` proves the inequality on \`|μ * v i|\` using \`abs_sum_le_sum_abs\` and the maximality of \`|v i|\`.
- The final argument shows \`|v i| > 0\` and rearranges the inequality to isolate \`|μ|\`.

Lean tactic notes for this proof sketch:

- \`obtain ⟨x, hx⟩\` is a structured form of \`rcases\` that pulls apart an existential or a conjunction.
- \`have h : ... := ...\` introduces a named intermediate lemma inside the proof.
- \`simp\` is often used to rewrite \`A.mulVec v\` to a sum over \`Finset.univ\`.
- \`calc\` chains equalities/inequalities in a readable block.
- \`abs_sum_le_sum_abs\` is the lemma \`|∑| ≤ ∑| |\` used to bound a sum by the sum of absolute values.
- \`mul_le_mul_of_nonneg_right\` and related lemmas handle inequalities when multiplying by a nonnegative term.
- To divide by \`|v i|\`, Lean typically uses a lemma like \`div_le_iff\` or \`mul_le_mul_left\` plus \`by have : 0 < |v i| := ...\`.

---

## Takeaway

- The first theorem identifies the **combinatorial structure** of the Huang matrix: its absolute values encode hypercube adjacency.
- The second theorem gives a **spectral bound**: any eigenvalue is controlled by the maximum absolute row sum.

Together, these results make it possible to translate combinatorial properties of the hypercube into spectral bounds on the Huang matrix.
`;

sectionContent[15] = `# Section 15: Spectral Radius Bound by Max Degree

This section proves a standard spectral radius bound: for a symmetric real matrix whose entries are supported on a simple graph and bounded by 1 in absolute value, the largest eigenvalue is at most the graph's maximum degree.

## Statement (informal)
Let \`A\` be an \`n x n\` real symmetric matrix. Let \`G\` be a simple graph on the same vertex set. Assume

- \`|A i j| <= 1\` when \`G.Adj i j\`, and
- \`|A i j| <= 0\` otherwise (so those entries are 0).

Then the largest eigenvalue of \`A\` is at most \`G.maxDegree\`.

In Lean, this is packaged as:

- \`A.IsSymm\` gives symmetry (required for real eigenvalues).
- \`sorted_eigenvalues A hA\` is a list of eigenvalues, sorted in **nondecreasing order** (i.e., ascending: \\(\\lambda_1 \\leq \\lambda_2 \\leq \\cdots \\leq \\lambda_n\\)).
- \`lambda_max\` is \`getLast\` of that list, i.e., the **largest** eigenvalue \\(\\lambda_n\\).
- The conclusion is \`lambda_max <= G.maxDegree\`.

**Type context**: \`A : Matrix (Fin n) (Fin n) ℝ\` is a real matrix indexed by \`Fin n\`. The hypothesis \`hA : A.IsSymm\` asserts \\(A = A^T\\).

Lean syntax notes that show up here:

- \`:\` is a type ascription, so \`A : Matrix (Fin n) (Fin n) ℝ\` reads "A has type ...".
- \`Matrix (Fin n) (Fin n) ℝ\` is Lean's function-style matrix type, i.e., a matrix is a function \`Fin n -> Fin n -> ℝ\`.
- \`Fin n\` is the finite type with elements \`0, 1, ..., n-1\`. So \`Fin n\` indexes rows and columns.
- \`ℝ\` is the real numbers type from \`Real\`.
- \`:=\` (when used) is definitional equality, introducing a definition. It differs from \`=\` (propositional equality).
- \`hA : A.IsSymm\` names a proof term \`hA\` of the proposition \`A.IsSymm\`. In Lean, proofs are just terms.

## Proof idea in one paragraph
The largest eigenvalue is bounded by the maximum absolute row sum (a standard lemma for eigenvalues). Each row sum is bounded by the number of neighbors, because each adjacent entry has absolute value at most 1 and each non-adjacent entry is 0. The neighbor count is the degree, which is at most the maximum degree. Chaining these inequalities gives the bound.

## How the Lean proof is organized

### 1. Use a general eigenvalue bound
The proof starts with a lemma already in the library:

\`\`\`lean
eigenvalue_le_max_row_sum A mu hmu
\`\`\`

Here \`hmu : Module.End.HasEigenvalue (Matrix.toLin' A) mu\` is a proof that \\(\\mu\\) is an eigenvalue of \\(A\\). The lemma returns an index \\(i\\) such that:
\\[
|\\mu| \\leq \\sum_j |A_{ij}|
\\]

This is the standard "eigenvalue bounded by max row sum" inequality, a consequence of the Gershgorin circle theorem.

Lean construct details in this line:

- \`Module.End.HasEigenvalue\` is a predicate on a linear map; it states "mu is an eigenvalue."
- \`Matrix.toLin' A\` coerces the matrix to a linear map (an element of \`Module.End\`), so eigenvalue facts apply.
- Function application is by juxtaposition: \`eigenvalue_le_max_row_sum A mu hmu\` means "apply the lemma to A, mu, hmu."
- The lemma's output is a dependent pair: it produces an index \`i\` with the row-sum inequality for that \`i\`.

### 2. Compare row sums to graph degree
For that specific row \`i\`, the code proves

\`\`\`
sum_j |A i j| <= sum_{j in G.neighborFinset i} 1
\`\`\`

because of the hypothesis \`h_adj\`:

- if \`G.Adj i j\`, then \`|A i j| <= 1\`
- otherwise \`|A i j| <= 0\`

So summing over all \`j\` is dominated by summing \`1\` over neighbors. This second sum is exactly the degree of \`i\`.

Lean constructs and tactics used here:

- \`G.Adj i j\` is the adjacency predicate of the graph. It lives in \`Prop\` (a proposition).
- \`G.neighborFinset i\` is the \`Finset\` of neighbors of \`i\`. \`Finset\` is a finite set with no duplicates.
- \`Finset.sum\` is written in Lean as \`∑ j in S, f j\`, and \`sum_j\` in the informal sketch corresponds to \`∑ j, ...\`.
- The inequality across sums is typically handled by \`Finset.sum_le_sum\`, a lemma that says if each summand is \`<=\`, then the total sum is \`<=\`.
- \`simp\` is a simplification tactic. It rewrites expressions using definitional equalities and tagged lemmas (e.g., rewriting \`|A i j|\` to \`0\` when \`h_adj\` says non-adjacent entries are zero).
- \`by\` introduces a term proof or tactic block. When you see \`by\`, it switches to tactic mode or term-style reasoning.
- \`have\` introduces a local lemma (a named intermediate result). It is often used to package bounds on each summand before applying \`Finset.sum_le_sum\`.

### 3. Move from degree to maximum degree
Finally, use the graph lemma

\`\`\`lean
G.degree_le_maxDegree i
\`\`\`

which gives

\`\`\`
G.degree i <= G.maxDegree
\`\`\`

Combining the inequalities yields

\`\`\`
mu <= G.maxDegree
\`\`\`

for any eigenvalue \`mu\`.

Lean notes:

- \`G.degree i\` is the degree as a natural number; \`G.maxDegree\` is the maximum over all vertices.
- \`G.degree_le_maxDegree i\` is a lemma returning a proof term of \`G.degree i <= G.maxDegree\`.
- Inequality chaining is often written with \`calc\` blocks in Lean (e.g., \`calc mu <= ... := ...; _ <= ... := ...\`).
- \`<=\` is a notation for \`LE.le\`; it uses typeclass instances to pick the right order (here, for \`ℝ\` or \`ℕ\`).

### 4. Apply the bound to the largest eigenvalue
The list \`sorted_eigenvalues A hA\` contains all eigenvalues. The proof shows every element of this list is bounded by \`G.maxDegree\`, so the last element (the maximum) is also bounded. The non-emptiness of the list is guaranteed by \`hn : n != 0\`.

## Practical reading of the Lean code

Key constructs:

- \`h_bound\`: proves every eigenvalue \`mu\` is \`<= G.maxDegree\`.
- \`h_sorted\`: lifts that bound to every element of \`sorted_eigenvalues\`.
- \`List.getLast_mem\` plugs the bound into \`lambda_max\`.

The only nontrivial steps are the sum estimate and the passage from an eigenvalue proof to the row-sum lemma. Those are handled by \`eigenvalue_le_max_row_sum\` and a short inequality chain using \`simp\` and \`Finset.sum_le_sum\`.

More Lean syntax detail for this step:

- \`sorted_eigenvalues A hA\` is a \`List ℝ\`. A list is a finite sequence, not a set; it can contain duplicates.
- \`List.getLast\` extracts the final element, but it needs a proof that the list is nonempty. That is why \`hn : n != 0\` appears.
- \`List.getLast_mem\` is a lemma that says the last element is a member of the list. This is used to transfer a bound that holds for all elements to the last one.
- A proof like \`h_sorted\` typically has the shape \`∀ μ ∈ sorted_eigenvalues A hA, μ <= G.maxDegree\`, which is a \`forall\` + membership statement. In Lean, this is written as \`∀ μ, μ ∈ ... -> μ <= ...\`.
- \`->\` is implication. So \`μ ∈ L -> μ <= M\` is "if μ is in L, then μ <= M."

## Why this is called a spectral radius bound
For symmetric real matrices, the spectral radius equals the largest absolute eigenvalue, and the largest eigenvalue is the last element of the sorted list. Thus bounding \`lambda_max\` bounds the spectral radius as well.

## Side note: Rayleigh quotient
The file ends with a reminder:

"The Rayleigh quotient of a vector x with respect to a matrix A is <x, Ax> / <x, x>."

This is the classical tool for characterizing eigenvalues of symmetric matrices, and it is another route to the same bound. The Lean proof above uses a library lemma instead of explicitly working with the Rayleigh quotient.
`;

sectionContent[16] = `# Rayleigh quotient and Courant-Fischer (Lean walkthrough)

This section introduces the Rayleigh quotient, the Courant-Fischer min-max characterization, and several supporting lemmas about eigenvalues of symmetric matrices. The Lean code works with real symmetric matrices and vectors indexed by \`Fin n\`.

## Rayleigh quotient

The Rayleigh quotient of a matrix \`A\` and a nonzero vector \`x\` is

\`\`\`
R_A(x) = (x^T A x) / (x^T x).
\`\`\`

In Lean:

\`\`\`lean
def rayleigh_quotient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (A.mulVec x) / dotProduct x x
\`\`\`

Lean syntax notes for this definition:

- \`def\` introduces a new constant (here, a function).
- \`{n : ℕ}\` is an implicit argument: Lean can often infer \`n\` from later arguments.
- \`Matrix (Fin n) (Fin n) ℝ\` is the type of \`n × n\` real matrices, indexed by \`Fin n\`.
- \`Fin n\` is the type of naturals \`< n\`; using it for indices ensures bounds are enforced by the type.
- \`x : Fin n → ℝ\` views a vector as a function from indices to coordinates.
- \`:=\` separates the name and type from the definition body.
- \`A.mulVec x\` is dot-notation for \`Matrix.mulVec A x\` (matrix–vector multiplication).
- \`dotProduct x y\` is the standard inner product; here it encodes \`xᵀ A x\` and \`xᵀ x\`.
- \`/\` is real division; the result is in \`ℝ\`.

Key properties used later:

- **Reindexing invariance.** If you change coordinates by a bijection of indices, the Rayleigh quotient is unchanged.
- **Zero padding and principal submatrices.** If you embed a vector supported on a subset \`S\` into the full space (padding with zeros outside \`S\`), its Rayleigh quotient with respect to \`A\` matches the Rayleigh quotient of the corresponding principal submatrix.

These facts let you compare eigenvalue information between a matrix and its principal submatrices.

## Courant-Fischer (inf-sup) definition

The Courant-Fischer min-max principle characterizes the \`k\`-th eigenvalue as a min over subspaces of a max of the Rayleigh quotient. The Lean definition in this file is the **inf-sup** form:

\`\`\`lean
def courant_fischer_inf_sup {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : ℝ :=
  ⨅ (V : Submodule ℝ (Fin n → ℝ)) (_ : Module.finrank ℝ V = k + 1),
    ⨆ (x : {x : V // x.1 ≠ 0}), rayleigh_quotient A x.1
\`\`\`

Lean syntax notes for this definition:

- \`⨅\` and \`⨆\` are the big infimum/supremum binders (\`iInf\`/\`iSup\`) from order theory.
- \`Submodule ℝ (Fin n → ℝ)\` is a linear subspace of the vector space \`Fin n → ℝ\`.
- \`(_ : Module.finrank ℝ V = k + 1)\` is an anonymous proof argument; it restricts the infimum to \`V\` of dimension \`k + 1\`.
- \`k : Fin n\` coerces to \`ℕ\` when used in arithmetic like \`k + 1\`.
- \`{x : V // x.1 ≠ 0}\` is a subtype: an element of \`V\` paired with a proof it is nonzero.
- \`x.1\` is the first projection of the subtype (the underlying vector in \`V\`); \`x.2\` would be the proof.
- \`rayleigh_quotient A x.1\` uses coercions: \`x.1 : V\` can be treated as a vector in \`Fin n → ℝ\`.

Read it as:

- take all subspaces \`V\` of dimension \`k + 1\`,
- for each \`V\` take the supremum of \`R_A(x)\` over nonzero \`x\` in \`V\`,
- then take the infimum of those suprema.

## Eigenbasis expansion and Rayleigh bounds

Much of the section expands vectors in an orthonormal eigenbasis and uses the sorted eigenvalues. The core idea:

If

\`\`\`
x = sum_i c_i v_i
\`\`\`

with \`v_i\` orthonormal eigenvectors, then

\`\`\`
R_A(x) = (sum_i c_i^2 * lambda_i) / (sum_i c_i^2).
\`\`\`

This immediately implies:

- **Upper bound by the largest eigenvalue.** If \`x != 0\`, then \`R_A(x) <= lambda_max\`.
- **Lower bound on a top-eigenspace span.** If \`x\` lives in the span of eigenvectors indexed \`i >= k\`, then \`R_A(x) >= lambda_k\`.

In Lean this appears as:

- \`rayleigh_le_max_eigenvalue\` for the upper bound.
- \`rayleigh_ge_of_mem_span_top\` for the lower bound on the top-eigenspace span.

Both proofs expand \`x\` in the orthonormal eigenbasis given by \`exists_orthonormal_basis_sorted\` and use monotonicity of the sorted eigenvalues.

Lean syntax notes for the surrounding constructs:

- \`span\` refers to \`Submodule.span\`, the subspace generated by a set of vectors.
- Names like \`rayleigh_ge_of_mem_span_top\` follow Lean convention: \`of\` indicates a lemma derived from a hypothesis like \`x ∈ span\`.
- \`exists_orthonormal_basis_sorted\` is a lemma providing a basis with extra structure; the \`exists\` prefix signals an existential statement.

## Dimension arguments and nontrivial intersection

To apply Courant-Fischer, we need a nonzero vector in the intersection of two subspaces. There are two related lemmas:

1. **Intersection dimension is positive.**
   If \`U\` has dimension \`n - k\` and \`V\` has dimension \`k + 1\` in an \`n\`-dimensional space, then \`U ∩ V\` is nontrivial.

2. **Specialized intersection for eigenvector spans.**
   In \`le_sup_rayleigh_of_dim_eq_succ\`, the code defines
   \`U = span {v_i | i >= k}\`.
   Since \`dim U = n - k\` and \`dim V = k + 1\`, the intersection contains a nonzero vector \`x\`.

This nonzero \`x\` is used to show that for any \`V\` of dimension \`k+1\`, the supremum of the Rayleigh quotient on \`V\` is at least \`lambda_k\`.

## Courant-Fischer inequality (one direction)

The lemma

\`\`\`lean
le_sup_rayleigh_of_dim_eq_succ
\`\`\`

proves the key inequality:

\`\`\`
lambda_k <= sup_{x in V, x != 0} R_A(x)
\`\`\`

for every \`V\` with \`dim V = k + 1\`. The proof is:

- pick a nonzero \`x\` in \`U ∩ V\` using the dimension argument,
- apply \`rayleigh_ge_of_mem_span_top\` to get \`R_A(x) >= lambda_k\`,
- conclude \`lambda_k <= sup_{x in V} R_A(x)\`.

This is the "inf-sup" half of Courant-Fischer.

## Principal submatrices

The file defines principal submatrices and reindexing:

\`\`\`lean
def principal_submatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Matrix S S ℝ :=
  A.submatrix Subtype.val Subtype.val


def principal_submatrix_fin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
  Matrix (Fin (Fintype.card {x // x ∈ S})) (Fin (Fintype.card {x // x ∈ S})) ℝ :=
  Matrix.reindex (Fintype.equivFin {x // x ∈ S}) (Fintype.equivFin {x // x ∈ S}) (principal_submatrix A S)
\`\`\`

Lean syntax notes for these definitions:

- \`Finset (Fin n)\` is a finite set of indices; it carries membership proofs.
- \`Matrix S S ℝ\` uses the subtype \`S\` as an index type; elements are of the form \`{x // x ∈ S}\`.
- \`A.submatrix f g\` reindexes \`A\` by functions \`f\` and \`g\`; \`Subtype.val\` forgets the membership proof.
- \`{x // x ∈ S}\` is the subtype of elements of \`Fin n\` that lie in \`S\`.
- \`Fintype.card {x // x ∈ S}\` is the cardinality of that subtype.
- \`Fintype.equivFin {x // x ∈ S}\` is a canonical equivalence between the subtype and \`Fin (card S)\`.
- \`Matrix.reindex\` transports a matrix along equivalences to change its index types.

There is a lemma that the reindexed principal submatrix remains symmetric if \`A\` is symmetric. This supports eigenvalue comparisons between a matrix and its principal submatrices using the Rayleigh quotient with zero-padded vectors.

## Takeaways

- The Rayleigh quotient is the core numerical bridge between vectors and eigenvalues.
- Reindexing and zero-padding allow precise transfer between submatrices and the original matrix.
- The Courant-Fischer min-max principle uses dimension arguments to guarantee vectors in intersections of subspaces.
- In Lean, these ideas appear as lemmas about reindexing, spans, finrank, and eigenbasis expansions.

If you want to extend this section, the next natural step is to formalize the full equality of Courant-Fischer (both directions), and then derive interlacing inequalities for eigenvalues of principal submatrices.

### Quick glossary of Lean keywords and tactic-style cues (as used in this section)

- \`def\`: define a new constant or function.
- \`:\`: type ascription (e.g., \`x : Fin n → ℝ\`).
- \`→\`: function type (e.g., \`Fin n → ℝ\` is the type of vectors).
- \`:=\`: separates a declaration from its defining term.
- \`//\`: subtype constructor; pairs a term with a proof of a property.
- \`.\`: field/namespace access via dot-notation (e.g., \`A.mulVec\`).
- \`⨅\`, \`⨆\`: infimum/supremum binders (\`iInf\`/\`iSup\`) from lattice theory.
- Tactic blocks are not shown in the snippets above; when present in Lean, they begin with \`by\` and use tactics (like \`simp\` for simplification or \`linarith\` for linear arithmetic) to build proofs.
`;

sectionContent[17] = `# Eigenvalue interlacing for principal submatrices

This section formalizes a standard interlacing fact for symmetric matrices:

> If you take a symmetric matrix \`A\` and restrict it to a principal submatrix \`subA\`
> indexed by a nonempty set \`S\`, then the **largest eigenvalue** of \`subA\` is **at least**
> the \`(m-1)\`-th eigenvalue of \`A\`, where \`m = |S|\`.

In Lean, the lemma is called \`eigenvalue_interlacing_max\`.

## The mathematical statement (informal)

Let:

- \`A\` be an \`n x n\` real symmetric matrix,
- \`S\` be a nonempty subset of \`{0,1,...,n-1}\` with \`m = |S|\`,
- \`subA\` be the principal submatrix of \`A\` indexed by \`S\`,
- \`evs_A\` be the sorted list of eigenvalues of \`A\` (in nondecreasing order),
- \`evs_sub\` be the sorted list of eigenvalues of \`subA\`.

Then:

\`\`\`
max_eigenvalue(subA) >= evs_A[m-1].
\`\`\`

In the Lean lemma, \`max_eigenvalue(subA)\` is expressed as
\`evs_sub.getLast\`.

This is the "top-end" half of eigenvalue interlacing: the largest eigenvalue of a
principal submatrix sits **above** the \`(m-1)\`-th eigenvalue of the full matrix.

**Lean syntax notes that show up here:**
- \`lemma eigenvalue_interlacing_max ... : ... := by\` introduces a named theorem and its proof. The \`: ...\` is the statement, and \`:= by\` switches to tactic mode.
- \`A : Matrix (Fin n) (Fin n) ℝ\` means \`A\` is a function \`Fin n → Fin n → ℝ\` (Lean’s matrix encoding).
- \`S : Finset (Fin n)\` is a finite set of indices; \`S.Nonempty\` is a \`Prop\` proof that \`S\` has an element.
- \`let m := S.card\` and \`let subA := ...\` bind local names in the statement. These \`let\`s are definitional abbreviations visible inside the lemma.
- \`evs_sub.getLast hne\` uses \`List.getLast\`, which requires a proof \`hne\` that the list is nonempty.
- The index \`⟨m - 1, ...⟩\` is a \`Fin\` value built from a natural number plus a proof that it is in range.

## How the proof works

The proof is a clean application of the min-max principle (a.k.a. Courant–Fischer) plus
a Rayleigh quotient comparison.

### 1. The subspace of supported vectors

Define a subspace \`V\` of \`R^n\` consisting of vectors supported on \`S\`:

- entries outside \`S\` are zero,
- dimension of \`V\` is \`m = |S|\`.

In Lean this is \`subspace_of_support S\` and the dimension lemma is
\`subspace_of_support_dim S\`.

### 2. Min-max principle gives a lower bound

The min-max principle says:

\`\`\`
ev_A[m-1] <= sup_{x in V, x != 0} R_A(x)
\`\`\`

where \`R_A(x)\` is the Rayleigh quotient of \`A\` at \`x\`.

Lean encapsulates this with \`le_sup_rayleigh_of_dim_eq_succ\`.

**Lean syntax and tactic details for this step:**
- \`set V := subspace_of_support S\` creates a definitional abbreviation *and* a local proof that the new name is equal to the original expression; it is useful when rewriting.
- \`have h_min_max : ... := by\` introduces a local lemma. \`have\` is how Lean names intermediate results.
- \`apply le_sup_rayleigh_of_dim_eq_succ ...\` tells Lean to use that lemma and turns its premises into subgoals.
- \`rw [Nat.sub_add_cancel ...]\` rewrites a goal using a lemma; \`rw\` replaces equals by equals.
- \`exact subspace_of_support_dim S\` closes a goal with a named lemma.

### 3. Rayleigh quotient is preserved on the submatrix

For any nonzero \`x\` in \`V\`, you can compress it to a vector \`y\` in \`R^m\`
by keeping only coordinates in \`S\`.

Then:

\`\`\`
R_A(x) = R_subA(y).
\`\`\`

This is the technical heart of the proof: it matches the quadratic form
of \`A\` on a supported vector with the quadratic form of the principal
submatrix.

In Lean this is the long lemma \`h_rayleigh_eq\`:

- it builds a coordinate map from \`x\` to \`y\`,
- shows the Rayleigh quotients agree.

**Lean syntax and tactic details for this step:**
- \`have h_rayleigh_eq : ∀ x ∈ V, x ≠ 0 → ∃ y, ... := by\` introduces a dependent \`∀\`/\`∃\` statement proved by tactics.
- \`intro x hx hx_ne_zero\` introduces universally quantified variables and hypotheses.
- \`obtain ⟨y, hy⟩ := ...\` destructs an \`∃\` (or other structure) into witnesses and proofs.
- \`refine' ⟨y, ?_, ?_⟩\` builds an \`∃\` goal by providing a witness and leaving placeholders.
- \`contrapose!\` turns a goal \`P → False\` or \`¬P\` into a goal about \`P\` by contrapositive; the bang version simplifies negations.
- \`unfold rayleigh_quotient\` expands a definition; it exposes the underlying dot products and matrix multiplication.
- \`simp\` and \`simp +decide\` simplify expressions using rewrite rules and decision procedures; \`+decide\` allows \`simp\` to discharge \`Decidable\` goals.
- \`split_ifs\` splits on \`if\` conditions, creating one subgoal per branch.
- \`ext i\` invokes extensionality (pointwise equality), common when proving two functions are equal.
- \`congr!\` is a stronger congruence tactic that reduces an equality of complex expressions to equalities of corresponding parts.

### 4. Rayleigh quotient is at most the max eigenvalue

For symmetric matrices, the Rayleigh quotient is always bounded by the
maximum eigenvalue:

\`\`\`
R_subA(y) <= max_eigenvalue(subA).
\`\`\`

Lean uses \`rayleigh_le_max_eigenvalue\` for this.

**Lean syntax and tactic details for this step:**
- \`have h_rayleigh_le_max : ∀ y, y ≠ 0 → ... := by\` is a typical way to package a reusable bound.
- \`intros y hy_nonzero\` is shorthand for multiple \`intro\`s.
- \`apply rayleigh_le_max_eigenvalue ...\` uses the bound lemma, leaving the nonzero and dimension side conditions as goals.
- \`exact ne_of_gt ...\` converts a strict inequality into a non-equality when a lemma expects \`≠\`.

### 5. Put it together

Chaining all inequalities:

\`\`\`
ev_A[m-1]
  <= sup_{x in V} R_A(x)
  =  sup_{y} R_subA(y)
  <= max_eigenvalue(subA).
\`\`\`

This yields the interlacing bound:

\`\`\`
max_eigenvalue(subA) >= ev_A[m-1].
\`\`\`

**Lean syntax and tactic details for the final glue:**
- \`refine le_trans h_min_max ?_\` applies transitivity of \`≤\`, leaving the second inequality as a goal.
- \`convert ciSup_le _\` changes the goal by definitional equality before applying \`ciSup_le\` (the \`≤\` bound for \`iSup\`).
- \`simp +zetaDelta\` expands \`let\` bindings and simplifies; \`zetaDelta\` is a simp lemma for \`let\`-bound definitions.
- \`grind\` is an automation tactic for first-order goals; it often closes routine set-membership and order subgoals.

## Key Lean objects and lemmas

- \`principal_submatrix_fin A S\`: principal submatrix indexed by \`S\`.
- \`principal_submatrix_fin_isSymm\`: symmetry is preserved.
- \`sorted_eigenvalues A hA\`: sorted eigenvalues list.
- \`subspace_of_support S\`: vectors supported on \`S\`.
- \`le_sup_rayleigh_of_dim_eq_succ\`: min-max inequality.
- \`rayleigh_le_max_eigenvalue\`: Rayleigh quotient bounded by max eigenvalue.

**Lean keyword/tactic glossary (as used in this proof):**
- \`by\`: starts a tactic block; what follows is a sequence of tactics producing the proof term.
- \`classical\`: opens classical logic (choice and excluded middle), often needed for \`Finset\`/\`Fintype\` constructions.
- \`set\` vs \`let\`: \`set\` introduces a name *and* a proof of definitional equality; \`let\` is a local abbreviation without a proof.
- \`have\`: introduces a local lemma with a name; often used to store intermediate bounds.
- \`apply\`: uses a lemma, turning its premises into new goals.
- \`rw\`: rewrite with an equality lemma.
- \`simp\`: simplify the goal using rewrite rules; \`simp_all\` simplifies all goals and hypotheses.
- \`exact\`: close a goal by providing a term of the required type.
- \`intro\`/\`intros\`: introduce variables/hypotheses for \`∀\` or \`→\` goals.
- \`obtain\`/\`rcases\`: destruct a structure or \`∃\` to get witnesses and proofs.
- \`refine\`/\`refine'\`: build a term with placeholders (\`?_\`) for remaining goals.
- \`unfold\`: expand a definition.
- \`ext\`: extensionality; reduce equality of functions/matrices to pointwise equality.
- \`convert\`: change the goal using definitional equality.
- \`aesop\`/\`grind\`: automation tactics for routine reasoning.

## Why this matters

Interlacing is a core tool in spectral graph theory and matrix analysis.
Here it is applied to principal submatrices, which correspond to restricting
the quadratic form to a coordinate subspace. This lemma isolates the
**maximum eigenvalue** bound that is later used to show large principal
submatrices inherit large eigenvalues.
`;

sectionContent[18] = `# Huang submatrix eigenvalue bounds

This section explains the Lean lemma
\`huang_submatrix_max_eigenvalue_ge_sqrt_n\`, which proves a lower bound on the
largest eigenvalue of a principal submatrix of the Huang matrix.

## The mathematical claim

Let \`n\` be a positive integer, and let \`S\` be a subset of the \`2^n\` indices with
\`|S| > 2^(n-1)\`. Consider the principal submatrix \`subA\` of the Huang matrix
\`A = huang_matrix_fin n\` obtained by restricting to the rows and columns in \`S\`.
Then the largest eigenvalue of \`subA\` is at least \`sqrt n\`.

In other words, any principal submatrix of size strictly larger than half the
rows must inherit an eigenvalue of size at least \`sqrt n\`.

## How the lemma is structured in Lean

The lemma has the following shape (simplified):

- \`subA\` is defined as \`principal_submatrix_fin (huang_matrix_fin n) S\`.
- \`h_subA\` is a proof that \`subA\` is symmetric, so its eigenvalues are real.
- \`evs_sub\` is the sorted list of eigenvalues of \`subA\`.
- The lemma concludes that \`evs_sub.getLast ... >= Real.sqrt n\`.

Lean uses \`getLast\` with a proof that the list of eigenvalues is nonempty.
That nonemptiness follows from the fact that \`S.card > 0\`.

## Lean syntax and tactic notes

Below are the Lean constructs that appear in the lemma, with short explanations
of what each keyword or tactic does.

- \`lemma name (args) : statement := by\` defines a theorem and begins a tactic
  proof block. The \`by\` keyword switches from term-style to tactic-style proof.
- \`def name (args) := term\` defines a reusable definition (used elsewhere in
  the file for auxiliary objects).
- \`let x := term\` introduces a local abbreviation. In the lemma statement, \`let\`
  binds \`subA\`, \`h_subA\`, and \`evs_sub\` so the goal can mention them without
  repeating long expressions.
- \`have h : P := by ...\` introduces a named intermediate claim \`h\` and proves it
  in a nested tactic block.
- \`apply lemma\` uses a lemma whose conclusion matches the current goal, turning
  the goal into its hypotheses. \`exact term\` finishes the goal with a proof
  term. \`refine\` is like \`exact\` but allows placeholders that are solved later.
- \`simp\` runs the simplifier on the goal; \`simp_all\` simplifies the goal and all
  hypotheses. The \`+decide\` flag tells \`simp\` to use \`decide\` to close goals
  about decidable propositions. \`rw [h]\` rewrites the goal using an equality
  \`h\`.
- \`convert\` changes the goal by a definitional equality (often after rewriting),
  letting you reuse a lemma whose conclusion is definitional equal to the goal.
- \`le_trans\` is the transitivity lemma for \`<=\`, used to chain inequalities.
- \`omega\` is an arithmetic decision tactic for Presburger arithmetic (linear
  inequalities over naturals and integers), used to discharge index bounds.
- \`List.getLast\` returns the last element of a list. It requires a proof that
  the list is nonempty; \`List.ne_nil_of_length_pos\` provides that from a proof
  that the length is positive.
- \`List.get ⟨i, hi⟩\` indexes a list using a \`Fin\` value. The notation \`⟨i, hi⟩\`
  constructs a \`Fin\` by bundling an index \`i\` with a proof \`hi\` that \`i\` is in
  range.
- \`List.replicate k a\` builds a list of \`k\` copies of \`a\`, and \`++\` concatenates
  lists. \`List.getElem_append\` is the lemma that describes how indexing behaves
  on a concatenated list (and is used to split into the left vs. right block of
  eigenvalues).

## Key ingredients in the proof

### 1) Interlacing of eigenvalues

The proof starts by applying a standard interlacing theorem for principal
submatrices:

- If you take a symmetric matrix \`A\` and a principal submatrix \`subA\`, then
  the eigenvalues of \`subA\` interlace those of \`A\`.
- In particular, the maximum eigenvalue of \`subA\` is at least the
  \`(m-1)\`-th eigenvalue of \`A\`, where \`m = |S|\`.

In Lean, this is implemented by \`eigenvalue_interlacing_max\`, which yields

\`\`\`
max_eigenvalue(subA) >=
  (sorted_eigenvalues A).get ⟨m - 1, ...⟩
\`\`\`

The index proof is bookkeeping: it shows \`m-1\` is within range because
\`m <= 2^n\` and \`m > 0\`.

### 2) Explicit spectrum of the Huang matrix

A separate lemma \`huang_eigenvalues_eq_list\` provides the full eigenvalue list
of the Huang matrix:

\`\`\`
[-sqrt n, ..., -sqrt n] (2^(n-1) times)
++
[+sqrt n, ..., +sqrt n] (2^(n-1) times)
\`\`\`

So the sorted eigenvalues are a block of negative values followed by a block of
positive values, with \`2^(n-1)\` copies of each.

### 3) Positioning the index

Because \`m = |S| > 2^(n-1)\`, the \`(m-1)\`-th eigenvalue of the full Huang matrix
falls in the positive block. That entry is exactly \`+sqrt n\`.

Lean encodes this by rewriting with the explicit eigenvalue list and using a
case split in \`List.getElem_append\` to show the index lands in the right half.

### 4) Final inequality

Combining interlacing with the explicit spectrum, the proof concludes

\`\`\`
max_eigenvalue(subA) >= sqrt n.
\`\`\`

This is exactly the statement in the lemma.

## Summary

The lemma is a standard application of eigenvalue interlacing and the explicit
spectrum of the Huang matrix. The key point is that any principal submatrix with
more than half the rows must inherit a large positive eigenvalue, because the
full matrix has \`2^(n-1)\` copies of \`+sqrt n\` and interlacing forces the submatrix
maximum to be at least one of them.
`;

sectionContent[19] = `# g_val and its level sets

This section defines a signed function \`g_val\` on the Boolean cube and then uses it to split the cube into two level sets, \`S_pos\` and \`S_neg\`. The key idea is that \`g_val\` always evaluates to either \`1\` or \`-1\`, so these level sets form a clean partition of all inputs.

## The definition of g_val

In Lean:

\`\`\`lean
def g_val {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℝ :=
  (if f x then -1 else 1) * chi Finset.univ x
\`\`\`

Interpretation:

- \`x : Fin n → Bool\` is a Boolean input of length \`n\`.
- \`chi Finset.univ x\` is the parity character on the full index set. Concretely, it is \`(-1)^{|{ i | x i = true }|}\`.
- \`(if f x then -1 else 1)\` flips the sign depending on whether the Boolean function \`f\` returns \`true\` at \`x\`.

So \`g_val f x\` is a signed value that combines the parity of \`x\` with the output of \`f\`. Both factors are \`±1\`, so the product is also \`±1\`.

Lean syntax notes for this definition:

- \`def\` introduces a new definition; \`g_val\` is the name being defined.
- \`{n : ℕ}\` is an implicit argument: Lean can infer \`n\` from context, so callers usually omit it. The type \`ℕ\` is the natural numbers.
- \`(f : (Fin n → Bool) → Bool)\` is a function argument. \`Fin n\` is the finite type \`{0, …, n-1}\`, so \`Fin n → Bool\` is an \`n\`-bit Boolean input, and \`f\` is a Boolean function on that cube.
- \`(x : Fin n → Bool)\` is another argument, explicitly the input point.
- \`: ℝ\` states the return type is real numbers.
- \`:=\` separates the definition head from its body.
- \`if f x then -1 else 1\` is Lean’s conditional; it has type \`ℝ\` here because both branches are real numbers.
- \`*\` is real multiplication.
- \`chi Finset.univ x\` is a function application; \`Finset.univ\` is the full finite set of all inputs, and \`chi\` is applied to it and then to \`x\`.

## Why g_val is always ±1

The parity character \`chi Finset.univ x\` is always \`1\` or \`-1\`. The conditional \`(if f x then -1 else 1)\` is also always \`1\` or \`-1\`. Their product therefore can only be \`1\` or \`-1\`.

This observation is the backbone of the level set definitions and the union/disjointness lemmas that follow.

## The positive and negative level sets

The section defines two finite sets of inputs:

\`\`\`lean
def S_pos {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.filter (fun x => g_val f x = 1) Finset.univ

def S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.filter (fun x => g_val f x = -1) Finset.univ
\`\`\`

- \`S_pos f\` collects all inputs where \`g_val f x = 1\`.
- \`S_neg f\` collects all inputs where \`g_val f x = -1\`.
- Both are subsets of the full Boolean cube \`Finset.univ\`.

Because \`g_val\` only takes values \`±1\`, every input belongs to exactly one of these sets.

Lean syntax notes for these definitions:

- \`Finset (Fin n → Bool)\` is the type of finite sets of Boolean inputs. \`Finset.univ\` is the universal finite set over that type.
- \`Finset.filter\` takes a predicate and keeps only elements that satisfy it.
- \`(fun x => g_val f x = 1)\` is an anonymous function (a lambda). It maps an input \`x\` to the proposition “\`g_val f x = 1\`”.
- \`=\` is definitional equality in Lean’s propositions; inside \`Finset.filter\` it is treated as a predicate.
- \`-1\` is a literal of type \`ℝ\` here, inferred from \`g_val f x : ℝ\`.

## The level sets cover the whole space

Lemma in Lean:

\`\`\`lean
lemma S_pos_union_S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) :
  S_pos f ∪ S_neg f = Finset.univ := by
  ...
\`\`\`

Informally: for any input \`x\`, \`g_val f x\` is either \`1\` or \`-1\`, so \`x\` must be in \`S_pos f\` or in \`S_neg f\`. The proof unfolds \`g_val\`, uses the fact that \`chi\` is also \`±1\`, and performs a case split on parity.

Lean syntax notes for this lemma statement:

- \`lemma\` declares a theorem with proof. The name is \`S_pos_union_S_neg\`.
- \`S_pos f ∪ S_neg f\` uses \`∪\` for finset union.
- \`=\` is equality between finsets.
- \`:= by\` switches into tactic mode, where the proof is built step-by-step.
- \`...\` is a placeholder in this writeup; in Lean, it stands for omitted proof steps.

## The level sets are disjoint

Lemma in Lean:

\`\`\`lean
lemma S_pos_disjoint_S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) :
  Disjoint (S_pos f) (S_neg f) := by
  exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
\`\`\`

This uses the fact that an element cannot satisfy both \`g_val f x = 1\` and \`g_val f x = -1\`. The \`linarith\` step closes the contradiction.

Lean syntax notes for the proof:

- \`Disjoint (S_pos f) (S_neg f)\` is the proposition that the two finsets have empty intersection.
- \`exact\` tells Lean to accept the following term as a complete proof of the goal.
- \`Finset.disjoint_filter.mpr\` is a lemma in “reverse” direction (\`mpr\` stands for *modus ponens reverse*), converting a disjointness goal into a pointwise proof about the filter predicates.
- \`fun _ _ _ _ =>\` introduces an anonymous function with four arguments. The underscores mean “unused arguments,” so Lean doesn’t require names for them.
- \`by linarith\` invokes the \`linarith\` tactic, which solves linear arithmetic contradictions automatically (here, \`1 = -1\` is impossible).
- The trailing \`;\` ends the tactic block (Lean allows it but it is optional here).

## Why this matters

The level sets \`S_pos\` and \`S_neg\` give a clean partition of the Boolean cube based on the sign of \`g_val\`. Later arguments can compare the sizes of these sets or relate them to sums like \`∑ x, g_val f x\`. For instance, if the sum is nonzero, then one of the sets must be larger than the other.

## Takeaways

- \`g_val\` is a signed combination of \`f\` and parity, always equal to \`1\` or \`-1\`.
- \`S_pos\` and \`S_neg\` are the level sets where \`g_val\` is positive or negative.
- These sets partition the entire space: they cover all inputs and are disjoint.
`;

sectionContent[20] = `# Why One Level Set Must Be Large

This section proves a simple but powerful counting fact: if a Boolean function has full degree, then one of its two "level sets" (where a related ±1-valued function is positive or negative) must contain **more than half** of the hypercube.

## The Lemma (informal)

Let \\(f : \\{0,1\\}^n \\to \\{0,1\\}\\) with \\(\\deg(f) = n\\) and \\(n \\neq 0\\). Recall from **Section 19** that \\(g_{\\text{val}}(f, x) = \\mathbf{1}_{f(x)} \\cdot \\chi_{[n]}(x)\\), which always equals \\(\\pm 1\\).

Define the level sets:
\\[
S_{\\text{pos}}(f) = \\{x \\in \\{0,1\\}^n : g_{\\text{val}}(f, x) = 1\\}
\\]
\\[
S_{\\text{neg}}(f) = \\{x \\in \\{0,1\\}^n : g_{\\text{val}}(f, x) = -1\\}
\\]

**Theorem**: At least one of these sets has size strictly greater than \\(2^{n-1}\\):
\\[
|S_{\\text{pos}}(f)| > 2^{n-1} \\quad \\text{or} \\quad |S_{\\text{neg}}(f)| > 2^{n-1}
\\]

## Intuition

Think of \\(g_{\\text{val}}(f, \\cdot)\\) as a \\(\\pm 1\\) labeling of the hypercube. The sum of all labels is:
\\[
\\sum_{x \\in \\{0,1\\}^n} g_{\\text{val}}(f, x) = |S_{\\text{pos}}| - |S_{\\text{neg}}|
\\]

If this sum is **nonzero**, then \\(|S_{\\text{pos}}| \\neq |S_{\\text{neg}}|\\). But the two sets partition the whole cube, so:
\\[
|S_{\\text{pos}}| + |S_{\\text{neg}}| = 2^n
\\]

If two non-negative integers sum to \\(2^n\\) and are unequal, one must exceed \\(2^{n-1}\\).

**Key fact** (from **Section 11**): For a full-degree function (\\(\\deg(f) = n\\)) and \\(n \\neq 0\\), the sum \\(\\sum_x g_{\\text{val}}(f, x) \\neq 0\\). This is because the sum equals (up to normalization) the top Fourier coefficient \\(\\hat{f}([n])\\), which is nonzero when \\(\\deg(f) = n\\).

## Proof Outline (Lean)

The Lean proof has two main parts.

### 1. Show the two level sets have different sizes

The proof computes the sum of \`g_val f\` by splitting over \`S_pos\` and \`S_neg\`:

- On \`S_pos\`, \`g_val f x = 1\`.
- On \`S_neg\`, \`g_val f x = -1\`.

So:

\`\`\`
Σ g_val f = |S_pos f| − |S_neg f|.
\`\`\`

The lemma \`g_val_sum_ne_zero f h_deg hn\` gives that this sum is nonzero, hence

\`\`\`
|S_pos f| ≠ |S_neg f|.
\`\`\`

Lean snippet (paraphrased):

\`\`\`lean
have h_card_ne : (S_pos f).card ≠ (S_neg f).card := by
  have h_card_ne : (Finset.sum Finset.univ (g_val f))
    = (S_pos f).card - (S_neg f).card := by
    -- split sum over S_pos and S_neg, then use g_val = ±1
    ...
  have := g_val_sum_ne_zero f h_deg hn
  aesop
\`\`\`

**Lean syntax/tactic notes (what each piece does):**

- \`have h_card_ne : ... := by\` introduces a **local lemma** named \`h_card_ne\` and starts a **tactic block** (\`by\`) to prove it.
- \`Finset.sum Finset.univ (g_val f)\` is a **finite sum** over the entire finite universe. \`Finset.univ\` is the finset of *all* elements of the finite type, and \`g_val f\` is the summand function.
- \`(S_pos f).card\` and \`(S_neg f).card\` are the **cardinalities** of the finsets \`S_pos f\` and \`S_neg f\`.
- \`= ... - ...\` is an equality in the target type of the sum. In Lean, this typically uses a coercion to an additive type (often \`ℤ\`) so the subtraction is well-defined; Lean inserts these coercions automatically when needed.
- \`...\` is a **placeholder** inside a proof block, signaling “proof details omitted here”; Lean would normally require actual steps (e.g., \`simp\`, \`rw\`, \`by_cases\`, etc.).
- \`have := g_val_sum_ne_zero f h_deg hn\` creates an **anonymous hypothesis** from the lemma \`g_val_sum_ne_zero\` specialized to \`f\` and the assumptions \`h_deg\` and \`hn\`.
- \`aesop\` is an **automation tactic** that tries to solve the goal using the available hypotheses and standard lemmas (a “best effort” proof search).

### 2. Use the partition of the cube

The sets \`S_pos\` and \`S_neg\` are disjoint and cover the whole hypercube, so:

\`\`\`
|S_pos f| + |S_neg f| = 2^n.
\`\`\`

Lean computes this using \`Finset.card_union_of_disjoint\` and the fact that the
universe of \`Fin n → Bool\` has size \`2^n\`. Since \`n ≠ 0\`, it rewrites

\`\`\`
2^n = 2 * 2^(n-1).
\`\`\`

So the sum of the two sizes is exactly twice \`2^(n-1)\`.

**Lean syntax/tactic notes (part 2):**

- \`Finset.card_union_of_disjoint\` is a lemma stating that if two finsets are **disjoint**, then the \`card\` of their union is the sum of their \`card\`s.
- The “universe” of inputs is typically expressed in Lean via \`Finset.univ\` (if you are in \`Finset\`) or \`Fintype.card\` (if you are counting the whole type). Both rely on the fact that \`Fin n → Bool\` is a finite type.
- The rewrite \`2^n = 2 * 2^(n-1)\` is usually done with rewriting lemmas like \`Nat.pow_succ\` (or \`pow_succ\`) plus \`Nat.succ_eq_add_one\` and \`Nat.mul_comm\`. Tactic-wise this is often a \`simp\` or \`rw\` step with those lemmas.

### 3. Conclude one side is larger than half

With:
- \\(|S_{\\text{pos}}| + |S_{\\text{neg}}| = 2 \\cdot 2^{n-1}\\), and
- \\(|S_{\\text{pos}}| \\neq |S_{\\text{neg}}|\\),

we can derive that one must exceed \\(2^{n-1}\\). Here's the explicit arithmetic:

**Proof**: Suppose for contradiction that both \\(|S_{\\text{pos}}| \\leq 2^{n-1}\\) and \\(|S_{\\text{neg}}| \\leq 2^{n-1}\\). Then:
\\[
|S_{\\text{pos}}| + |S_{\\text{neg}}| \\leq 2 \\cdot 2^{n-1}
\\]
But we know \\(|S_{\\text{pos}}| + |S_{\\text{neg}}| = 2 \\cdot 2^{n-1}\\), so equality holds throughout. This means \\(|S_{\\text{pos}}| = 2^{n-1}\\) and \\(|S_{\\text{neg}}| = 2^{n-1}\\), contradicting \\(|S_{\\text{pos}}| \\neq |S_{\\text{neg}}|\\).

Therefore, at least one of \\(|S_{\\text{pos}}| > 2^{n-1}\\) or \\(|S_{\\text{neg}}| > 2^{n-1}\\) must hold. Lean closes this with \`grind\`.

**Lean syntax/tactic note (part 3):**

- \`grind\` is another **automation tactic** (from the \`grind\`/\`simp\`/\`linarith\` family) that tries to solve arithmetic and logical goals by combining rewriting and decision procedures. Here it discharges the final “one side is larger” arithmetic goal.

## Takeaway

The full-degree condition forces a global imbalance in the ±1 labeling \`g_val f\`. Once you know the two level sets partition the hypercube, that imbalance means one level set must contain **strictly more than half** of all inputs.

This fact is a recurring lever: it turns algebraic information (nonzero sum) into a combinatorial guarantee (a large level set).
`;

sectionContent[21] = `# Hypercube Graph Definition and Properties

This section formalizes the n-dimensional hypercube graph in Lean and records a few key properties that connect adjacency, parity, and induced subgraphs. The vertices are Boolean vectors of length \`n\`, modeled as functions \`Fin n -> Bool\`.

## 1. Defining the hypercube graph

In Lean, the hypercube graph is defined as a \`SimpleGraph\` whose adjacency relation holds exactly when two vertices differ in exactly one coordinate:

\`\`\`lean
def hypercube_graph (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun x y => (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1)
\`\`\`

Key ideas:

- \`Fin n → Bool\` is the type of Boolean strings of length \`n\` (each index \`i : Fin n\` gives a bit).
- \`Finset.univ\` is the finite set of all indices \`i : Fin n\`.
- \`Finset.filter (fun i => x i ≠ y i)\` selects the coordinates where \`x\` and \`y\` differ.
- The adjacency condition is that this set has cardinality 1, i.e., Hamming distance 1.

Lean details:

- \`def\` introduces a new definition. Here it defines a function \`hypercube_graph\` that takes \`n\` and returns a graph.
- \`ℕ\` is the type of natural numbers.
- \`:\` is type ascription, so \`(n : ℕ)\` reads "n has type Nat".
- \`SimpleGraph (Fin n → Bool)\` is a graph whose vertices are functions \`Fin n → Bool\`.
- \`:=\` separates the definition name from its value.
- \`SimpleGraph.fromRel\` builds a simple graph from a symmetric, irreflexive relation.
- \`fun x y => ...\` is lambda notation, defining the adjacency predicate as a function of two vertices.
- The expression \`(Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1\` is a Boolean proposition. \`filter\` restricts \`Finset.univ\`, \`.card\` is its size, and \`= 1\` is equality in \`ℕ\`.
- \`x i\` means applying the function \`x\` to the index \`i\`.

The lemma \`hypercube_graph_adj\` immediately unfolds this definition:

\`\`\`lean
lemma hypercube_graph_adj {n : ℕ} (x y : Fin n → Bool) :
  (hypercube_graph n).Adj x y ↔
    (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1 := by
  simp [hypercube_graph]
\`\`\`

This lemma is a convenience rule for rewriting adjacency into a cardinality statement.

Lean details:

- \`lemma\` introduces a named theorem.
- \`{n : ℕ}\` is an implicit argument; Lean can usually infer it.
- \`(x y : Fin n → Bool)\` are explicit arguments.
- \`:\` starts the statement being proved.
- \`↔\` is logical equivalence ("if and only if").
- \`(hypercube_graph n).Adj x y\` uses dot-notation to access the adjacency relation of a graph.
- \`:= by\` starts a tactic proof block.
- \`simp [hypercube_graph]\` runs the simplifier and tells it to unfold \`hypercube_graph\` using the definition in the bracketed list.

## 2. Neighbor parity and the \`chi\` sign

The file uses a parity-based function \`chi\` (defined elsewhere) and proves that neighbors in the hypercube have opposite \`chi\` values:

\`\`\`lean
lemma chi_univ_neighbor {n : ℕ} (x y : Fin n → Bool)
  (h_adj : (hypercube_graph n).Adj x y) :
  chi Finset.univ x = -chi Finset.univ y := by
  -- proof omitted
\`\`\`

Intuition:

- If \`x\` and \`y\` differ in exactly one coordinate, then the number of \`true\` bits changes by 1.
- Therefore the parity flips, and a parity-based sign like \`chi\` must change sign.

Lean details:

- A line break after the lemma name is just formatting; the arguments continue on the next line.
- \`(h_adj : (hypercube_graph n).Adj x y)\` is a hypothesis that \`x\` and \`y\` are adjacent.
- \`chi Finset.univ x\` applies \`chi\` to the full set of indices and the vertex \`x\`.
- The unary \`-\` is numeric negation; here it flips the sign.
- \`:= by\` again signals a tactic proof (omitted in the file).

## 3. Relating \`g_val\` and function changes on edges

The lemma \`g_val_neighbor_eq_iff_f_ne\` states that along a hypercube edge, equality of \`g_val\` is equivalent to \`f\` changing value:

\`\`\`lean
lemma g_val_neighbor_eq_iff_f_ne {n : ℕ}
  (f : (Fin n → Bool) → Bool) (x y : Fin n → Bool)
  (h_adj : (hypercube_graph n).Adj x y) :
  g_val f x = g_val f y ↔ f x ≠ f y := by
  -- proof omitted
\`\`\`

This is used later to relate graph-theoretic degrees to sensitivity. The key point is that adjacency plus a sign flip controls how \`g_val\` behaves across an edge.

Lean details:

- \`(f : (Fin n → Bool) → Bool)\` is a Boolean function on vertices.
- \`g_val f x\` uses function application; \`g_val\` is defined elsewhere.
- \`≠\` is inequality. \`f x ≠ f y\` is the proposition that the Boolean values differ.

## 4. Sensitivity as degree in induced subgraphs

Two lemmas connect Boolean function sensitivity to degrees in induced subgraphs of the hypercube. The positive and negative level sets are written \`S_pos f\` and \`S_neg f\`.

For \`S_pos\`:

\`\`\`lean
lemma sensitivity_at_x_eq_degree_in_S_pos {n : ℕ}
  (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : x ∈ S_pos f) :
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y) Finset.univ).card =
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S_pos f) Finset.univ).card := by
  -- proof omitted
\`\`\`

And similarly for \`S_neg\`:

\`\`\`lean
lemma sensitivity_at_x_eq_degree_in_S_neg {n : ℕ}
  (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : x ∈ S_neg f) :
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y) Finset.univ).card =
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S_neg f) Finset.univ).card := by
  -- proof omitted
\`\`\`

Interpretation:

- The left side counts neighbors where \`f\` changes value (sensitivity at \`x\`).
- The right side counts neighbors staying inside the same level set, i.e., degree in the induced subgraph on \`S_pos\` or \`S_neg\`.
- These lemmas show that in the appropriate level set, sensitivity is exactly a graph degree.

Lean details:

- \`x ∈ S_pos f\` and \`x ∈ S_neg f\` are membership propositions in finite sets.
- \`∧\` is logical conjunction, so the filter conditions require adjacency and an additional property.
- \`Finset.filter\` again selects neighbors that satisfy the conjunction.
- \`card\` is used on both sides, so the lemma is a statement about equality of counts.

## 5. Induced hypercube graphs and reindexing

The file defines induced hypercube graphs and also a version where vertices are reindexed by \`Fin (2^n)\`.

Induced subgraph on a finite set \`S\` of Boolean vectors:

\`\`\`lean
def induced_hypercube_graph {n : ℕ} (S : Finset (Fin n → Bool)) :
  SimpleGraph {x // x ∈ S} :=
  SimpleGraph.induce (S : Set (Fin n → Bool)) (hypercube_graph n)
\`\`\`

Hypercube graph on \`Fin (2^n)\` using the equivalence between bitstrings and numbers:

\`\`\`lean
def hypercube_graph_fin (n : ℕ) : SimpleGraph (Fin (2^n)) :=
  (hypercube_graph n).map (boolFunEquivFin n).toEmbedding
\`\`\`

And the induced graph reindexed by \`Fin (card S)\`:

\`\`\`lean
def induced_hypercube_graph_fin_card {n : ℕ} (S : Finset (Fin (2^n))) :
  SimpleGraph (Fin (Fintype.card {x // x ∈ S})) :=
  let G := SimpleGraph.induce (S : Set (Fin (2^n))) (hypercube_graph_fin n)
  let equiv := Fintype.equivFin {x // x ∈ S}
  G.map equiv.toEmbedding
\`\`\`

These definitions allow later spectral arguments to be stated over standard finite types (\`Fin k\`) while preserving the hypercube adjacency structure.

Lean details:

- \`{x // x ∈ S}\` is a subtype: pairs of \`x\` with a proof that \`x ∈ S\`.
- \`SimpleGraph.induce\` restricts a graph to a subset of vertices.
- \`(S : Set (Fin n → Bool))\` coerces a \`Finset\` to a \`Set\` using the canonical coercion.
- \`.map\` transfers a graph along an embedding between vertex types.
- \`(boolFunEquivFin n).toEmbedding\` is the embedding underlying an equivalence between Boolean functions and \`Fin (2^n)\`.
- \`let G := ...\` and \`let equiv := ...\` introduce local definitions within the term; they are in scope for the final expression.
- \`Fintype.card\` gives the number of elements in a finite type.
- \`Fintype.equivFin\` produces an equivalence between a finite type and \`Fin (card ...)\`.

## Takeaways

- The hypercube graph is defined by Hamming distance 1 using a filtered index set.
- Adjacency implies parity flips, which shows up as a sign change in \`chi\`.
- Sensitivity at a point is captured by degree in an induced subgraph of the hypercube.
- The hypercube can be reindexed to \`Fin (2^n)\` and induced subgraphs can be reindexed to \`Fin (card S)\` without losing adjacency information.
`;

sectionContent[22] = `# Restriction to Subcubes

This section defines **restriction** of a Boolean function to a subset of coordinates. This is a fundamental operation that allows us to focus on a "subcube" by fixing some variables to constant values.

## What is restriction?

Given a Boolean function

\`\`\`
f : (Fin n → Bool) → Bool
\`\`\`

and a subset of coordinates \`S : Finset (Fin n)\`, we can **restrict** \`f\` by:

- allowing the coordinates in \`S\` to vary freely, and
- fixing all coordinates outside \`S\` to some assignment \`z : Fin n → Bool\`.

In Lean, the restriction is:

\`\`\`lean
def restriction {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (z : Fin n → Bool) :
  (Fin (Fintype.card {x // x ∈ S}) → Bool) → Bool :=
  fun y => f (fun i =>
    if h : i ∈ S
    then y ((Fintype.equivFin {x // x ∈ S}).symm ⟨i, h⟩)
    else z i)
\`\`\`

### Lean syntax walkthrough

Below is a Lean-oriented explanation of the constructs in the definition above. This is about *syntax and semantics* of Lean, not the math.

- \`def restriction ... := ...\` introduces a new definition named \`restriction\`. The \`:=\` separates the name/signature from the body.
- \`{n : ℕ}\` is an *implicit* argument (Lean will infer \`n\` when possible). \`ℕ\` is the type of natural numbers.
- \`(f : (Fin n → Bool) → Bool)\` is a *named argument* with a type. \`→\` is the function type constructor, so \`Fin n → Bool\` is a Boolean assignment on \`n\` coordinates, and \`(Fin n → Bool) → Bool\` is a Boolean function on such assignments.
- \`S : Finset (Fin n)\` is a finite set of indices. \`Fin n\` is the type of natural numbers strictly less than \`n\`.
- \`(z : Fin n → Bool)\` is the fixed assignment outside \`S\`.
- The result type
  \`\`\`
  (Fin (Fintype.card {x // x ∈ S}) → Bool) → Bool
  \`\`\`
  says the restricted function takes inputs indexed by a set of size \`|S|\`. \`Fintype.card\` gives the cardinality of a finite type, and \`{x // x ∈ S}\` is a *subtype* (elements \`x\` with a proof they are in \`S\`).
- \`fun y => ...\` is an anonymous function. This is Lean's lambda syntax.
- \`f (fun i => ...)\` applies \`f\` to a *constructed* full assignment. The inner \`fun i => ...\` is a function of a coordinate \`i : Fin n\`.
- \`if h : i ∈ S then ... else ...\` is a *dependent if*: it not only checks membership, it also binds \`h\` as a proof of \`i ∈ S\` in the \`then\` branch.
- \`⟨i, h⟩\` is a *subtype constructor*: it builds an element of \`{x // x ∈ S}\` from \`i : Fin n\` and the proof \`h\`.
- \`(Fintype.equivFin {x // x ∈ S})\` is an equivalence between the subtype and \`Fin (Fintype.card {x // x ∈ S})\`. The \`.symm\` field takes the inverse direction of that equivalence.
- \`y ((Fintype.equivFin {x // x ∈ S}).symm ⟨i, h⟩)\` means: convert the \`S\`-element \`⟨i, h⟩\` to an index in \`Fin |S|\`, then feed it to \`y\`.
- \`else z i\` uses the fixed assignment on coordinates not in \`S\`.

The input to the restricted function is a Boolean assignment only on the coordinates in \`S\`. The code constructs a full assignment \`x : Fin n → Bool\` by:

- using the input \`y\` on indices in \`S\` (via an equivalence between \`S\` and \`Fin |S|\`),
- using \`z\` on indices outside \`S\`.

Then it evaluates \`f x\`.

## Intuition: plugging in constants

Intuitively, a restriction is the usual "plug in constants outside S" operation. If you have a Boolean function on 5 variables and you fix variables 2 and 4 to specific values, you get a new function on the remaining 3 variables.

Example: Suppose \`f(x₀, x₁, x₂) = x₀ XOR x₁ XOR x₂\` and we restrict to \`S = {0, 2}\` with \`z₁ = true\`. Then:

\`\`\`
restriction f S z (y₀, y₁) = y₀ XOR true XOR y₁ = NOT(y₀ XOR y₁)
\`\`\`

The restricted function depends only on the free variables in \`S\`.

## Why restriction matters

Restriction is a key tool for several reasons:

1. **Fourier analysis**: Restricting to a subset \`S\` that supports a top-degree Fourier coefficient turns that coefficient into the "full set" coefficient of the restricted function.

2. **Induction**: Many proofs about Boolean functions proceed by restricting to smaller subcubes.

3. **Sensitivity bounds**: As we'll see in the next section, sensitivity cannot increase under restriction, which allows us to transfer bounds.

## Connection to Fourier coefficients

A crucial lemma (proved elsewhere) states:

\`\`\`lean
lemma exists_restriction_fourier_coeff_univ_ne_zero (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
  (hS : fourier_coeff f S ≠ 0) :
  ∃ z, fourier_coeff (restriction f S z) Finset.univ ≠ 0
\`\`\`

Lean syntax notes for this statement:

- \`lemma\` introduces a named theorem; it behaves like \`theorem\` but is often used for helper results.
- \`(hS : fourier_coeff f S ≠ 0)\` is a hypothesis argument. \`≠\` is inequality, and \`0\` is the zero element of the coefficient type inferred by Lean.
- The colon \`:\` before the final line separates the hypotheses from the conclusion.
- \`∃ z, ...\` is the existential quantifier (“there exists \`z\`”). In Lean it is a binder that introduces \`z\` in the conclusion.
- \`Finset.univ\` is the finite set of all elements of the relevant finite type (here, all coordinates in the restricted domain).

This says: if \`f\` has a nonzero Fourier coefficient at \`S\`, then there exists a restriction \`z\` such that the restricted function has a nonzero coefficient at the full set (i.e., \`Finset.univ\` for the smaller domain).

This is exactly what we need to connect the degree of \`f\` to the degree of its restrictions.

## Takeaways

- Restriction fixes variables outside a set \`S\` and keeps only the \`S\`-coordinates free.
- The Lean definition uses an explicit equivalence to map between the restricted and full coordinate spaces.
- Restriction is essential for transferring Fourier-analytic information between functions of different dimensions.
`;

sectionContent[23] = `# Sensitivity Monotonicity Under Restriction

This section proves the key monotonicity fact: **restricting a function cannot increase its sensitivity**. This lemma is the bridge that lets us transfer sensitivity bounds from restricted functions back to the original.

## The Lemma

\`\`\`lean
lemma sensitivity_restriction_le {n : ℕ} (f : (Fin n → Bool) → Bool)
  (S : Finset (Fin n)) (z : Fin n → Bool) :
  sensitivity (restriction f S z) ≤ sensitivity f
\`\`\`

In plain language: the sensitivity of the restricted function is at most the sensitivity of the original function.

Lean syntax notes for the statement above:
- \`lemma\` introduces a named theorem; its name is \`sensitivity_restriction_le\`.
- \`{n : ℕ}\` is an **implicit** argument (curly braces); Lean will infer \`n\` when possible. \`ℕ\` is the type of natural numbers.
- \`(f : (Fin n → Bool) → Bool)\` declares a function taking a Boolean input on \`Fin n\` (i.e., a length-\`n\` Boolean vector) and returning a \`Bool\`.
- \`Fin n\` is the finite type \`{0, …, n-1}\`; \`Fin n → Bool\` is a function assigning a Boolean to each coordinate.
- \`(S : Finset (Fin n))\` is a finite set of indices; \`Finset\` is the computational (decidable) finite set type.
- \`(z : Fin n → Bool)\` is a fixed Boolean assignment used for coordinates outside \`S\`.
- The colon \`:\` before the last line separates the hypotheses from the conclusion.
- \`sensitivity (restriction f S z) ≤ sensitivity f\` is the goal; \`≤\` is the usual order on \`ℕ\`.
- Function application is by juxtaposition: \`restriction f S z\` means \`restriction\` applied to \`f\`, then \`S\`, then \`z\`.

## Why it's true: intuition

Recall from **Section 22** that \`restriction f S z\` is a function on \\(\\{0,1\\}^{|S|}\\), where we fix coordinates outside \\(S\\) to the values in \\(z\\).

**Key observation about Hamming distance**: In the restricted space \\(\\{0,1\\}^{|S|}\\), two inputs \\(y, y'\\) are neighbors (Hamming distance 1) if they differ in exactly one coordinate of \\(S\\). This corresponds exactly to neighbors in the full space \\(\\{0,1\\}^n\\) that:
- Differ in exactly one coordinate
- That coordinate is in \\(S\\)
- Both inputs agree with \\(z\\) outside \\(S\\)

So the restricted space has **fewer** neighbors to consider (only flips within \\(S\\)), not more.

Every input \\(y \\in \\{0,1\\}^{|S|}\\) to the restricted function corresponds to a full input \\(x \\in \\{0,1\\}^n\\), obtained by:
\\[
x_i = \\begin{cases} y_j & \\text{if } i \\text{ is the } j\\text{-th element of } S \\\\ z_i & \\text{if } i \\notin S \\end{cases}
\\]

Since the restriction only explores a subset of inputs and a subset of bit flips, it cannot create more sensitive directions than the original function already had.

## Proof structure in Lean

The Lean proof formalizes this intuition by:

### 1. Unfold sensitivity as a supremum

Recall that sensitivity is defined as:

\`\`\`lean
def sensitivity (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.sup Finset.univ (fun x =>
    (Finset.filter (fun y => hammingDist x y = 1 ∧ f x ≠ f y) Finset.univ).card)
\`\`\`

Lean syntax notes for the definition above:
- \`def\` introduces a definition (as opposed to a theorem).
- \`: ℕ\` annotates the return type; \`:=\` starts the definition body.
- \`Finset.sup\` takes a finite set and a function, returning the supremum (maximum) value of that function over the set.
- \`Finset.univ\` is the full finite set of all elements of the relevant finite type (here, all \`x : Fin n → Bool\`).
- \`fun x => ...\` is a lambda (anonymous function) mapping each \`x\` to its number of sensitive neighbors.
- \`Finset.filter\` keeps only elements satisfying a predicate; here it filters neighbors \`y\` with Hamming distance 1 and output flip.
- \`hammingDist x y = 1\` uses \`=\` for equality; \`∧\` is logical “and”.
- \`f x ≠ f y\` uses \`≠\` for inequality.
- \`( ... ).card\` takes the cardinality of the filtered finite set.

So we need to show that the supremum over the restricted domain is at most the supremum over the full domain.

### 2. Map restricted inputs to full inputs

For each restricted input \`y\`, construct the corresponding full input \`x\` by combining \`y\` on \`S\` with \`z\` outside \`S\`. This is the inverse of the restriction operation.

### 3. Show sensitive neighbors inject

The key step is constructing an **injection** from sensitive neighbors of \\(y\\) in the restricted domain to sensitive neighbors of \\(x\\) in the full domain.

Let \\(y' \\in \\{0,1\\}^{|S|}\\) be a sensitive neighbor of \\(y\\) for the restricted function, meaning:
- \\(y'\\) differs from \\(y\\) in exactly one coordinate \\(j \\in S\\)
- \\((\\text{restriction } f\\, S\\, z)(y) \\neq (\\text{restriction } f\\, S\\, z)(y')\\)

Construct \\(x' \\in \\{0,1\\}^n\\) by: keeping \\(z\\) outside \\(S\\), and using \\(y'\\) on \\(S\\).

Then \\(x'\\) differs from \\(x\\) in exactly one coordinate (the same \\(j\\)), and by definition of restriction:
\\[
f(x) = (\\text{restriction } f\\, S\\, z)(y) \\neq (\\text{restriction } f\\, S\\, z)(y') = f(x')
\\]

So \\(x'\\) is a sensitive neighbor of \\(x\\) for \\(f\\). This map \\(y' \\mapsto x'\\) is injective because distinct \\(y'\\) give distinct \\(x'\\).

### 4. Apply cardinality comparison

Since there's an injection from sensitive neighbors in the restricted domain to sensitive neighbors in the full domain:

\`\`\`lean
(restricted sensitive neighbors at y).card ≤ (sensitive neighbors at x).card
\`\`\`

Taking the supremum over all \`y\` and noting that each maps to some \`x\`:

\`\`\`lean
sup_y (restricted sensitivity at y) ≤ sup_x (sensitivity at x)
\`\`\`

This gives the desired inequality.

## Why this matters for the main proof

This monotonicity lemma is crucial in the final argument:

1. We find a top-degree Fourier coefficient at some set \`S\`.
2. We restrict to \`S\` so that the restricted function has full degree equal to \`|S|\`.
3. We apply the "full-degree implies large sensitivity" bound to the restricted function.
4. We use \`sensitivity_restriction_le\` to lift this bound back to the original function:

\`\`\`
sensitivity f ≥ sensitivity (restriction f S z) ≥ √(degree (restriction f S z)) = √(degree f)
\`\`\`

Without monotonicity, we couldn't transfer the bound from the restriction to the original function.

## Takeaways

- Sensitivity is monotone under restriction: it can only stay the same or decrease.
- The Lean proof mirrors the combinatorial argument by building an explicit injection from restricted sensitive neighbors to original sensitive neighbors.
- This lemma is the key bridge between the full-degree case (where spectral methods give bounds) and the general case (arbitrary Boolean functions).
`;

sectionContent[24] = `# Final theorem: sensitivity_conjecture

This section proves the final statement of the sensitivity conjecture in the Boolean setting:

\`\`\`lean
theorem sensitivity_conjecture {n : ℕ} (f : (Fin n → Bool) → Bool) :
  (sensitivity f : ℝ) ≥ Real.sqrt (degree f)
\`\`\`

In mathematical notation:
\\[
s(f) \\geq \\sqrt{\\deg(f)}
\\]

**Fourier basis convention**: Throughout this project, we use the \\(\\{0,1\\}\\)-valued encoding for Boolean functions (see **Section 4**). The Fourier degree is defined using the parity characters \\(\\chi_S\\) (see **Section 3**).

The proof is a clean chain of earlier lemmas. Below is a walkthrough of the ideas and how the Lean proof stitches them together.

---

## Goal and strategy

We want to show the sensitivity of any Boolean function is at least the square root of its Fourier degree. The proof splits into two cases:

1. \`degree f = 0\` (constant function): then the inequality is trivial.
2. \`degree f ≠ 0\`: find a top-degree Fourier coefficient, restrict to that support so the full coefficient is nonzero, deduce the restricted function has degree equal to the number of variables, apply a degree-to-sensitivity lower bound, then lift back to the original function using monotonicity under restriction.

The proof is essentially:

\`\`\`
sensitivity f
  >= sensitivity (restriction f S z)
  >= sqrt (degree (restriction f S z))
  =  sqrt (degree f)
\`\`\`

---

## Step-by-step explanation

### 1) Case split on \\(\\deg(f) = 0\\)

Lean starts with:

\`\`\`lean
cases eq_or_ne (degree f) 0 <;> simp_all +decide
\`\`\`

**Lean syntax notes**:
- \`eq_or_ne a b\` is a lemma producing \`a = b ∨ a ≠ b\`.
- \`cases\` performs case analysis on that disjunction, creating two goals: one for \`degree f = 0\` and one for \`degree f ≠ 0\`.
- \`<;>\` is tactic sequencing that applies the following tactic(s) to *all* goals generated so far.
- \`simp_all\` simplifies the goal and all hypotheses using the simp lemma set and any available rewrite rules.
- \`+decide\` extends simplification with \`decide\`, which discharges decidable propositions by computation.

**Why the degree-0 case is trivial**: If \\(\\deg(f) = 0\\), then \\(\\sqrt{\\deg(f)} = 0\\). Since sensitivity is always \\(\\geq 0\\) (it's a natural number), the inequality \\(s(f) \\geq 0\\) holds trivially.

**What degree 0 means**: A function has \\(\\deg(f) = 0\\) if and only if all Fourier coefficients \\(\\hat{f}(S)\\) with \\(|S| \\geq 1\\) are zero. This means \\(f\\) depends only on the empty set of variables, i.e., \\(f\\) is a **constant function**. Constant functions have sensitivity 0.

The rest of the proof assumes \\(\\deg(f) \\neq 0\\), i.e., \\(f\\) is non-constant.

### 2) Choose a maximal-support nonzero Fourier coefficient

The degree is defined as the maximum cardinality of a subset \`S\` with nonzero Fourier coefficient \`fourier_coeff f S\`.

The proof unfolds the definition and uses finite set arguments to pick an \`S\` with:

- \`fourier_coeff f S ≠ 0\`
- \`S.card\` is maximal among those with nonzero coefficient

Lean uses \`Set.exists_max_image\` after establishing finiteness of the set of such \`S\`. This yields:

\`\`\`
∃ k, k = degree f ∧ ∃ S, S.card = k ∧ fourier_coeff f S ≠ 0
\`\`\`

This is the “there is a top-degree coefficient” step.

**Lean syntax notes (existentials and pattern matching)**:
- \`obtain ⟨k, hk⟩ : ∃ k, ... := by ...\` extracts a witness \`k\` and its proof \`hk\` from an existential statement.
- The \`⟨⟩\` syntax constructs or destructs tuples/existentials; it is Lean’s canonical “pair” notation.
- Projections like \`hk.1\` and \`hk.2\` pick out components of nested conjunctions/tuples.
- \`unfold degree\` expands the definition of \`degree\` so the \`Finset\`/\`Set\` machinery is visible to subsequent tactics.

### 3) Restrict to the top-degree support

Using the lemma \`exists_restriction_fourier_coeff_univ_ne_zero\`, we select a restriction \`z\` such that for the restricted function

\`\`\`
 g = restriction f S z
\`\`\`

the Fourier coefficient at the full set is nonzero:

\`\`\`
fourier_coeff g Finset.univ ≠ 0
\`\`\`

Intuitively: after fixing all variables outside \`S\`, the coefficient on the remaining variables becomes the top coefficient of the restricted function.

**Lean syntax notes (application and \`exact\`)**:
- Function application is written by juxtaposition: \`restriction f S z\` means \`restriction\` applied to \`f\`, \`S\`, and \`z\`.
- \`Finset.univ\` is the universal finite set for the current finite type (here, the remaining variables after restriction).
- \`exact\` supplies a term that matches the goal exactly; in this step the lemma \`exists_restriction_fourier_coeff_univ_ne_zero f S hS_fourier\` directly provides the witness and proof.

### 4) Degree of the restricted function is exactly \`|S|\`

Now the lemma \`degree_eq_n_of_fourier_coeff_univ_ne_zero\` applies:

\`\`\`
 degree (restriction f S z) = S.card
\`\`\`

Because the “full set” coefficient is nonzero, the restricted function has full degree on its remaining variables.

**Lean syntax notes (\`have\` and automation)**:
- \`have h_deg_g : ... := by ...\` introduces a named local lemma; the \`by\` opens a tactic block to construct it.
- An underscore \`_\` is an implicit argument placeholder; Lean infers it from context.
- \`aesop\` is a proof automation tactic that tries to solve goals using a database of lemmas and heuristics.

### 5) Sensitivity lower bound in the full-degree case

Earlier we proved:

\`\`\`
sensitivity_ge_sqrt_degree_of_degree_eq_n
\`\`\`

This gives:

\`\`\`
sensitivity (restriction f S z) ≥ sqrt (degree (restriction f S z))
\`\`\`

Combine with the degree equality from Step 4 to get a lower bound in terms of \`S.card\`.

**Lean syntax notes (casts and \`Real.sqrt\`)**:
- \`(sensitivity (restriction f S z) : ℝ)\` uses a type coercion from \`ℕ\` to \`ℝ\`, guided by the explicit \`: ℝ\` annotation.
- \`Real.sqrt\` is the real square root; simplification tactics can rewrite expressions involving it when given nonnegativity facts.

### 6) Lift the bound back to the original function

Restrictions cannot increase sensitivity, so:

\`\`\`
sensitivity f ≥ sensitivity (restriction f S z)
\`\`\`

This is exactly \`sensitivity_restriction_le\` (casted to \`ℝ\` in the proof).

**Lean syntax notes (\`exact_mod_cast\`)**:
- \`exact_mod_cast\` applies a lemma after automatically inserting the necessary coercions between related numeric types (like \`ℕ\` and \`ℝ\`) and rewriting with coercion lemmas.
- It is especially handy for inequalities that are true in \`ℕ\` but the goal is in \`ℝ\`.

### 7) Finish with arithmetic and rewriting

The final line \`grind\` closes the goal by chaining the inequalities and rewriting \`S.card = degree f\`.

**Lean syntax notes (\`grind\`)**:
- \`grind\` is a finishing tactic that combines rewriting, simplification, and arithmetic reasoning.
- Here it uses the accumulated \`≥\` chain and the equality \`S.card = degree f\` to solve the final real inequality.

---

## How the pieces fit together

- **Fourier degree** is characterized by the largest subset \`S\` with a nonzero Fourier coefficient.
- **Restriction** focuses on that subset and turns its coefficient into the \`univ\` coefficient of the restricted function.
- **Full-degree sensitivity bound** shows that for any function whose top coefficient is at \`univ\`, sensitivity is at least \`sqrt degree\`.
- **Monotonicity of sensitivity under restriction** lets us transfer the bound back to the original function.

That chain is exactly the proof structure in Lean.

---

## Lean proof outline (annotated)

\`\`\`
cases eq_or_ne (degree f) 0 <;> simp_all +decide
-- pick top-degree Fourier coefficient
obtain ⟨k, hk⟩ : ∃ k, k = degree f ∧ ∃ S, S.card = k ∧ fourier_coeff f S ≠ 0 := by
  unfold degree; ...
-- restrict so univ coefficient is nonzero
obtain ⟨S, hS_card, hS_fourier⟩ := hk.2
obtain ⟨z, hz⟩ : ∃ z, fourier_coeff (restriction f S z) Finset.univ ≠ 0 := by
  exact exists_restriction_fourier_coeff_univ_ne_zero f S hS_fourier
-- degree of restriction is full
have h_deg_g : degree (restriction f S z) = S.card := by
  have := degree_eq_n_of_fourier_coeff_univ_ne_zero _ hz; aesop
-- sensitivity bound on restricted function
have h_sens_g : (sensitivity (restriction f S z) : ℝ) ≥ Real.sqrt (degree (restriction f S z)) := by
  have := sensitivity_ge_sqrt_degree_of_degree_eq_n (restriction f S z); aesop
-- sensitivity monotonicity under restriction
have h_sens_f : (sensitivity f : ℝ) ≥ (sensitivity (restriction f S z) : ℝ) := by
  exact_mod_cast sensitivity_restriction_le f S z
-- finish
 grind
\`\`\`

This completes the formal proof of the sensitivity conjecture in the project.
`;

export default sectionContent;
