/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7e83d196-3bcb-4261-9529-a1b59902ab4b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma sensitivity_bound_from_level_set {n : ℕ} (f : (Fin n → Bool) → Bool)
  (hn : n ≠ 0) (S0 : Finset (Fin n → Bool))
  (h_eq :
    ∀ x ∈ S0,
      (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S0)
          Finset.univ).card =
        (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y)
          Finset.univ).card)
  (hS0 : S0.card > 2^(n-1)) :
  (sensitivity f : ℝ) ≥ Real.sqrt n
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1238dc9a-cd4f-41ea-bfbd-67d339f150a4

The following was proved by Aristotle:

- theorem sensitivity_ge_sqrt_degree_of_degree_eq_n {n : ℕ} (f : (Fin n → Bool) → Bool) (h_deg : degree f = n) (hn : n ≠ 0) :
  (sensitivity f : ℝ) ≥ Real.sqrt n

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
Formalized the proof of the Sensitivity Conjecture (Huang 2019). Defined the Huang matrix, proved its spectral properties, established the interlacing results, and connected the spectral bound to the sensitivity via the induced subgraph of the hypercube. Proved that any boolean function of degree n has sensitivity at least sqrt(n).
-/

import Mathlib
import Archive.Sensitivity


import Mathlib.Tactic.GeneralizeProofs


namespace Harmonic.GeneralizeProofs

-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs

def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'

partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs

partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

set_option linter.mathlibStandardSet false

open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

/-! ## Section 1: Core definitions
  Sensitivity, Fourier coefficients, and degree for Boolean functions.
-/

/-
The sensitivity of a boolean function f is the maximum over all inputs x of the number of neighbors y of x such that f(x) ≠ f(y).
-/
def sensitivity {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.sup Finset.univ (fun x => Finset.card (Finset.filter (fun y => (Finset.card (Finset.filter (fun i => x i ≠ y i) Finset.univ) = 1) ∧ f x ≠ f y) Finset.univ))

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

/-! ## Section 6: Level-set combinatorics
  Build the large level set of g and relate it to sensitivity counts.
-/

/-
$\EE(g) \neq 0$
-/
theorem g_expectation_nonzero {n : ℕ} (f : (Fin n → Bool) → Bool)
  (h_deg : degree f = n) (hn : n ≠ 0) :
  let g := fun x => (if f x then 1 else 0) * chi Finset.univ x
  (Finset.sum Finset.univ g) ≠ 0 := by
    have h_fourier_coeff : ∃ S : Finset (Fin n), fourier_coeff f S ≠ 0 ∧
        S.card = n := by
      contrapose! h_deg
      refine' ne_of_lt (lt_of_le_of_lt (Finset.sup_le _) _)
      exacts [ n - 1,
        fun S hS =>
          Nat.le_sub_one_of_lt <|
            lt_of_le_of_ne (le_trans (Finset.card_le_univ _) <|
              by simp) <| h_deg S <| by simpa using hS,
        Nat.pred_lt hn ]
    obtain ⟨S, hS₁, hS₂⟩ := h_fourier_coeff
    simp_all +decide [fourier_coeff]
    have := Finset.eq_of_subset_of_card_le (Finset.subset_univ S)
    aesop

/-
The sum of g_val is non-zero if f has full degree.
-/
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

/-
Definitions of the positive and negative level sets of g.
-/
def S_pos {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.filter (fun x => g_val f x = 1) Finset.univ

def S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.filter (fun x => g_val f x = -1) Finset.univ

/-
S_pos and S_neg cover the whole space.
-/
lemma S_pos_union_S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) :
  S_pos f ∪ S_neg f = Finset.univ := by
    ext x; simp [S_pos, S_neg];
    unfold g_val;
    split_ifs <;> unfold chi <;> simp +decide;
    · cases Nat.mod_two_eq_zero_or_one ( Finset.card ( Finset.filter ( fun i => x i = true ) Finset.univ ) ) <;> simp +decide [ * ];
    · cases Nat.mod_two_eq_zero_or_one ( Finset.card ( Finset.filter ( fun i => x i = true ) Finset.univ ) ) <;> simp +decide [ * ]

/-
S_pos and S_neg are disjoint.
-/
lemma S_pos_disjoint_S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) :
  Disjoint (S_pos f) (S_neg f) := by
    exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;

/-
One of the level sets of g has size > 2^(n-1).
-/
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

/-! ## Section 7: Hypercube graph and adjacency bridge
  Define the hypercube graph and relate it to `Sensitivity.Q.adjacent`.
-/

/-
Definition of the hypercube graph.
-/
def hypercube_graph (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun x y => (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1)

lemma hypercube_graph_adj {n : ℕ} (x y : Fin n → Bool) :
  (hypercube_graph n).Adj x y ↔ (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1 := by
    simp [hypercube_graph];
    -- If x and y are not equal, then there must be at least one index where they differ. The cardinality of the set of such indices being 1 means there's exactly one difference, which implies x and y are not equal. Conversely, if the cardinality is 1, then there's exactly one difference, so x and y can't be equal.
    apply Iff.intro;
    · simp_all +decide [ eq_comm ];
    · aesop

lemma existsUnique_iff_card_eq_one {n : ℕ} (x y : Fin n → Bool) :
  (∃! i, x i ≠ y i) ↔
    (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1 := by
  classical
  constructor
  · intro h
    rcases h with ⟨i, hi, huniq⟩
    apply Finset.card_eq_one.mpr
    refine ⟨i, ?_⟩
    apply Finset.ext
    intro j
    constructor
    · intro hj
      have hj' : x j ≠ y j := (Finset.mem_filter.mp hj).2
      have : j = i := huniq j hj'
      simp [this]
    · intro hj
      have : j = i := by simpa using hj
      subst this
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  · intro h
    rcases Finset.card_eq_one.mp h with ⟨i, hi⟩
    have hi' : x i ≠ y i := by
      have : i ∈ Finset.filter (fun i => x i ≠ y i) Finset.univ := by
        simp [hi]
      exact (Finset.mem_filter.mp this).2
    refine ⟨i, hi', ?_⟩
    intro j hj
    have hj' : j ∈ Finset.filter (fun i => x i ≠ y i) Finset.univ := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    have : j ∈ ({i} : Finset (Fin n)) := by
      simpa [hi] using hj'
    simpa using this

@[simp] lemma mem_adjacent_iff_hypercube_adj {n : ℕ} (x y : Fin n → Bool) :
  y ∈ (Sensitivity.Q.adjacent (n := n) x) ↔ (hypercube_graph n).Adj x y := by
  classical
  constructor
  · intro h
    have h' : ∃! i, x i ≠ y i := by
      simpa [Sensitivity.Q.adjacent] using h
    have hcard :
        (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1 :=
      (existsUnique_iff_card_eq_one (x := x) (y := y)).1 h'
    exact (hypercube_graph_adj x y).2 hcard
  · intro h
    have hcard :
        (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1 :=
      (hypercube_graph_adj x y).1 h
    have h' : ∃! i, x i ≠ y i :=
      (existsUnique_iff_card_eq_one (x := x) (y := y)).2 hcard
    simpa [Sensitivity.Q.adjacent] using h'

/-
Neighbors in the hypercube graph have opposite chi values.
-/
lemma chi_univ_neighbor {n : ℕ} (x y : Fin n → Bool) (h_adj : (hypercube_graph n).Adj x y) :
  chi Finset.univ x = -chi Finset.univ y := by
    -- Since x and y differ by exactly one bit, their parities are opposite.
    have h_parity : (Finset.filter (fun i => x i) Finset.univ).card % 2 ≠ (Finset.filter (fun i => y i) Finset.univ).card % 2 := by
      have h_parity : (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1 := by
        exact (hypercube_graph_adj x y).mp h_adj;
      -- Since x and y differ by exactly one bit, the number of 1s in x and y differ by 1.
      have h_diff : (Finset.filter (fun i => x i = true) Finset.univ).card + (Finset.filter (fun i => y i = true) Finset.univ).card = (Finset.filter (fun i => x i ≠ y i) Finset.univ).card + 2 * (Finset.filter (fun i => x i = true ∧ y i = true) Finset.univ).card := by
        rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
        rw [ Finset.card_filter ];
        rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext i ; by_cases hi : x i <;> by_cases hj : y i <;> simp +decide [ hi, hj ] ;
      omega;
    unfold chi; aesop;

/-
g values are equal for neighbors iff f values are different.
-/
lemma g_val_neighbor_eq_iff_f_ne {n : ℕ} (f : (Fin n → Bool) → Bool) (x y : Fin n → Bool) (h_adj : (hypercube_graph n).Adj x y) :
  g_val f x = g_val f y ↔ f x ≠ f y := by
    have h_univ_neighbor : chi Finset.univ x = -chi Finset.univ y := by
      exact chi_univ_neighbor x y h_adj;
    unfold g_val;
    cases f x <;> cases f y <;> simp +decide [ * ];
    · unfold chi at *;
      split_ifs at * <;> norm_num at *;
    · unfold chi; split_ifs <;> norm_num;

/-
For x in S_pos, the sensitivity at x equals the degree of x in the induced subgraph on S_pos.
-/
lemma sensitivity_at_x_eq_degree_in_S_pos {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : x ∈ S_pos f) :
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y) Finset.univ).card =
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S_pos f) Finset.univ).card := by
    -- Apply the lemma `g_val_neighbor_eq_iff_f_ne` to each neighbor `y` of `x`.
    have h_neighbor : ∀ y : Fin n → Bool, (hypercube_graph n).Adj x y → (f x ≠ f y ↔ y ∈ S_pos f) := by
      intros y hy_adj
      have h_g_eq : g_val f x = g_val f y ↔ f x ≠ f y := by
        exact g_val_neighbor_eq_iff_f_ne f x y hy_adj;
      unfold S_pos at *; aesop;
    exact congr_arg Finset.card ( Finset.ext fun y => by specialize h_neighbor y; aesop )

/-
For x in S_neg, the sensitivity at x equals the degree of x in the induced subgraph on S_neg.
-/
lemma sensitivity_at_x_eq_degree_in_S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : x ∈ S_neg f) :
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y) Finset.univ).card =
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S_neg f) Finset.univ).card := by
    unfold S_neg at *;
    congr! 2;
    ext y;
    constructor <;> intro h;
    · have := chi_univ_neighbor x y h.1; unfold g_val at *; aesop;
    · have := g_val_neighbor_eq_iff_f_ne f x y h.1; aesop;

/-! ## Section 8: Full-degree case (core bound)
  Combine spectral bounds, graph degrees, and level-set structure to prove
  sensitivity ≥ sqrt(n).
-/

lemma sensitivity_bound_from_level_set {n : ℕ} (f : (Fin n → Bool) → Bool)
  (hn : n ≠ 0) (S0 : Finset (Fin n → Bool))
  (h_eq :
    ∀ x ∈ S0,
      (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S0)
          Finset.univ).card =
        (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y)
          Finset.univ).card)
  (hS0 : S0.card > 2^(n-1)) :
  (sensitivity f : ℝ) ≥ Real.sqrt n := by
    classical
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    let H : Set (Sensitivity.Q (m + 1)) := (S0 : Set (Fin (m + 1) → Bool))
    letI : DecidablePred (Membership.mem H) := Classical.decPred _
    letI : Fintype H := Subtype.fintype (Membership.mem H)
    let Hfin : Finset (Sensitivity.Q (m + 1)) := H.toFinset
    have hH : Hfin.card ≥ 2^m + 1 := by
      have h' : 2^m + 1 ≤ S0.card := Nat.succ_le_iff.mpr hS0
      have hHfin : Hfin = S0 := by
        ext y
        simp [Hfin, H]
      simpa [hHfin] using h'
    have hH' : H.toFinset.card ≥ 2^m + 1 := by
      simpa [Hfin] using hH
    obtain ⟨q, hqH, hqdeg⟩ := Sensitivity.huang_degree_theorem (m := m) (H := H) hH'
    have hqS0 : q ∈ S0 := by
      simpa [H] using hqH
    have h_eq_finset :
        H.toFinset ∩ q.adjacent.toFinset =
          Finset.filter (fun y => (hypercube_graph (m + 1)).Adj q y ∧ y ∈ S0) Finset.univ := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_inter.mp hy with ⟨hyH, hyadj⟩
        have hyH' : y ∈ H := by
          simpa using hyH
        have hyadj' : y ∈ q.adjacent := by
          simpa using hyadj
        have hyadj'' :
            (hypercube_graph (m + 1)).Adj q y :=
          (mem_adjacent_iff_hypercube_adj (x := q) (y := y)).1 hyadj'
        refine Finset.mem_filter.mpr ?_
        exact ⟨Finset.mem_univ _, ⟨hyadj'', by simpa [H] using hyH'⟩⟩
      · intro hy
        rcases Finset.mem_filter.mp hy with ⟨_, hy⟩
        rcases hy with ⟨hyadj, hyS⟩
        apply Finset.mem_inter.mpr
        refine ⟨?_, ?_⟩
        · simpa [H] using hyS
        · exact (Set.mem_toFinset.mpr ((mem_adjacent_iff_hypercube_adj (x := q) (y := y)).2 hyadj))
    have hdeg' :
        Real.sqrt (m + 1) ≤
          ((Finset.filter (fun y => (hypercube_graph (m + 1)).Adj q y ∧ y ∈ S0) Finset.univ).card : ℝ) := by
      simpa [h_eq_finset] using hqdeg
    have h_eq_q :
        (Finset.filter (fun y => (hypercube_graph (m + 1)).Adj q y ∧ y ∈ S0) Finset.univ).card =
          (Finset.filter (fun y => (hypercube_graph (m + 1)).Adj q y ∧ f q ≠ f y)
            Finset.univ).card := by
      exact h_eq q hqS0
    have hdeg'' :
        Real.sqrt (m + 1) ≤
          ((Finset.filter (fun y => (hypercube_graph (m + 1)).Adj q y ∧ f q ≠ f y)
            Finset.univ).card : ℝ) := by
      simpa [h_eq_q] using hdeg'
    have h_sens_nat :
        (Finset.filter (fun y => (hypercube_graph (m + 1)).Adj q y ∧ f q ≠ f y)
            Finset.univ).card ≤ sensitivity f := by
      unfold sensitivity
      simpa [hypercube_graph_adj] using
        (Finset.le_sup (s := Finset.univ)
          (f := fun x =>
            Finset.card
              (Finset.filter
                (fun y =>
                  (Finset.card (Finset.filter (fun i => x i ≠ y i) Finset.univ) = 1) ∧
                    f x ≠ f y)
                Finset.univ))
          (b := q) (by simp))
    have h_sens_real :
        ((Finset.filter (fun y => (hypercube_graph (m + 1)).Adj q y ∧ f q ≠ f y)
            Finset.univ).card : ℝ) ≤ (sensitivity f : ℝ) := by
      exact_mod_cast h_sens_nat
    have hdeg''' :
        Real.sqrt (m + 1) ≤
          ((Finset.filter (fun y => (hypercube_graph (m + 1)).Adj q y ∧ f q ≠ f y)
            Finset.univ).card : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using hdeg''
    exact by
      grind

/-
A boolean function of degree n has sensitivity at least sqrt(n).
-/
theorem sensitivity_ge_sqrt_degree_of_degree_eq_n {n : ℕ}
  (f : (Fin n → Bool) → Bool) (h_deg : degree f = n) (hn : n ≠ 0) :
  (sensitivity f : ℝ) ≥ Real.sqrt n := by
    -- Pick the large level set (S_pos or S_neg).
    have h_large := exists_large_level_set f h_deg hn
    cases h_large with
    | inl hpos =>
        apply sensitivity_bound_from_level_set (f := f) hn (S_pos f)
        · intro x hx
          simpa using (sensitivity_at_x_eq_degree_in_S_pos f x hx).symm
        · exact hpos
    | inr hneg =>
        apply sensitivity_bound_from_level_set (f := f) hn (S_neg f)
        · intro x hx
          simpa using (sensitivity_at_x_eq_degree_in_S_neg f x hx).symm
        · exact hneg

/-
The sensitivity of a restriction is at most the sensitivity of the original function.
-/
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

/-
The Fourier coefficient of f at S is the average of the Fourier coefficients of the restrictions at univ.
-/
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

/-
If the Fourier coefficient at S is non-zero, there is a restriction with non-zero Fourier coefficient at univ.
-/
lemma exists_restriction_fourier_coeff_univ_ne_zero {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (hS : fourier_coeff f S ≠ 0) :
  ∃ z : Fin n → Bool, fourier_coeff (restriction f S z) Finset.univ ≠ 0 := by
    rw [ fourier_coeff_restriction_avg ] at hS;
    exact not_forall.mp fun h => hS <| by rw [ Finset.sum_eq_zero fun _ _ => h _ ] ; norm_num;

/-
If the Fourier coefficient at univ is non-zero, the degree is n.
-/
lemma degree_eq_n_of_fourier_coeff_univ_ne_zero {n : ℕ} (f : (Fin n → Bool) → Bool) (h : fourier_coeff f Finset.univ ≠ 0) :
  degree f = n := by
    refine' le_antisymm _ _;
    · exact Finset.sup_le fun S hS => Nat.le_trans ( Finset.card_le_univ _ ) ( by norm_num );
    · refine' le_trans _ ( Finset.le_sup <| Finset.mem_filter.mpr ⟨ Finset.mem_univ Finset.univ, h ⟩ );
      norm_num

/-
A boolean function of degree n has sensitivity at least sqrt(n).
-/
theorem sensitivity_conjecture {n : ℕ} (f : (Fin n → Bool) → Bool) :
  (sensitivity f : ℝ) ≥ Real.sqrt (degree f) := by
    cases eq_or_ne ( degree f ) 0 <;> simp_all +decide;
    -- Let k = degree f. There exists a set S with |S| = k and f_hat(S) ≠ 0.
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
    -- By `exists_restriction_fourier_coeff_univ_ne_zero`, there exists z such that the restriction g = restriction f S z has g_hat(univ) ≠ 0.
    obtain ⟨S, hS_card, hS_fourier⟩ := hk.2
    obtain ⟨z, hz⟩ : ∃ z : Fin n → Bool, fourier_coeff (restriction f S z) Finset.univ ≠ 0 := by
      exact exists_restriction_fourier_coeff_univ_ne_zero f S hS_fourier
    -- By `degree_eq_n_of_fourier_coeff_univ_ne_zero`, degree g = k.
    have h_deg_g : degree (restriction f S z) = S.card := by
      have := degree_eq_n_of_fourier_coeff_univ_ne_zero ( restriction f S z ) hz; aesop;
    -- By `sensitivity_ge_sqrt_degree_of_degree_eq_n`, sensitivity g ≥ √k.
    have h_sens_g : (sensitivity (restriction f S z) : ℝ) ≥ Real.sqrt (degree (restriction f S z)) := by
      have := sensitivity_ge_sqrt_degree_of_degree_eq_n ( restriction f S z ) ; aesop;
    -- By `sensitivity_restriction_le`, sensitivity f ≥ sensitivity g.
    have h_sens_f : (sensitivity f : ℝ) ≥ (sensitivity (restriction f S z) : ℝ) := by
      exact_mod_cast sensitivity_restriction_le f S z;
    grind
