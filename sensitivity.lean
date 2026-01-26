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

/-
Equivalence between Bool x alpha and alpha + alpha.
-/
def boolProdEquivSum_custom {α : Type*} : Bool × α ≃ α ⊕ α where
  toFun := fun p => if p.1 then Sum.inr p.2 else Sum.inl p.2
  invFun := fun s => match s with
    | Sum.inl a => (false, a)
    | Sum.inr a => (true, a)
  left_inv := by
    rintro ⟨ _ | _, _ ⟩ <;> simp +decide
  right_inv := by
    rintro (a | a) <;> rfl

/-
Equivalence between functions from Fin (n+1) to alpha and pairs of (alpha, function from Fin n to alpha).
-/
def finSuccEquiv_custom (n : ℕ) (α : Type*) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun f := (f 0, f ∘ Fin.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    ext i
    refine Fin.cases ?_ ?_ i <;> simp
  right_inv p := by
    ext <;> simp

/-
Equivalence between functions from Fin (n+1) to Bool and the sum of two copies of functions from Fin n to Bool.
-/
def finSuccEquiv_huang_custom (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Fin n → Bool) ⊕ (Fin n → Bool) :=
  Equiv.trans
    (finSuccEquiv_custom n Bool)
    (boolProdEquivSum_custom)

/-
The Huang matrix A_n is defined recursively. A_0 is 0. A_{n+1} is a block matrix with A_n on the diagonal, I on the off-diagonal, and -A_n on the other diagonal, reindexed to match the boolean hypercube indices.
-/
def huang_matrix (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  match n with
  | 0 => 0
  | n + 1 => Matrix.reindex (finSuccEquiv_huang_custom n).symm (finSuccEquiv_huang_custom n).symm
      (Matrix.fromBlocks (huang_matrix n) (1 : Matrix _ _ ℝ) (1 : Matrix _ _ ℝ) (-huang_matrix n))

/-
The square of the Huang matrix A_n is n times the identity matrix.
-/
theorem huang_matrix_sq (n : ℕ) : (huang_matrix n) ^ 2 = (n : ℝ) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) := by
  induction' n with n ih;
  · norm_num [ sq ];
    exact mul_eq_zero_of_left rfl (huang_matrix 0)
  · -- By definition of huang_matrix, we have:
    have h_def : huang_matrix (n + 1) = Matrix.reindex (finSuccEquiv_huang_custom n).symm (finSuccEquiv_huang_custom n).symm (Matrix.fromBlocks (huang_matrix n) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (-huang_matrix n)) := by
      rfl;
    -- By definition of matrix multiplication and the induction hypothesis, we can expand the square of the block matrix.
    have h_expand : (Matrix.fromBlocks (huang_matrix n) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (-huang_matrix n)) ^ 2 = Matrix.fromBlocks ((n + 1 : ℝ) • 1) 0 0 ((n + 1 : ℝ) • 1) := by
      simp_all +decide [ sq, Matrix.fromBlocks_multiply ];
      norm_num [ add_smul, add_comm ];
    simp_all +decide [ sq, Matrix.reindex_apply ];
    ext i j; simp +decide [ Matrix.submatrix, Matrix.smul_eq_diagonal_mul ] ;
    by_cases hij : i = j <;> simp +decide [ hij, Matrix.one_apply ]

/-
The eigenvalues of the Huang matrix square to n.
-/
theorem huang_matrix_eigenvalues {n : ℕ} {μ : ℝ} (h : Module.End.HasEigenvalue (Matrix.toLin' (huang_matrix n)) μ) : μ ^ 2 = n := by
  obtain ⟨ v, hv ⟩ := h.exists_hasEigenvector;
  -- Since $A^2 = nI$, we have $A^2 v = n v$.
  have h_sq : (Matrix.toLin' (huang_matrix n)) (Matrix.toLin' (huang_matrix n) v) = (n : ℝ) • v := by
    convert congr_arg ( fun x : Matrix ( Fin n → Bool ) ( Fin n → Bool ) ℝ => x.mulVec v ) <| huang_matrix_sq n using 1;
    · simp +decide [ sq ];
    · simp +decide [ Matrix.smul_eq_diagonal_mul ];
  -- Since $v$ is an eigenvector of $A$, we have $A v = \mu v$.
  have h_eigen : (Matrix.toLin' (huang_matrix n)) v = μ • v := by
    cases hv ; aesop;
  simp_all +decide [ sq ];
  exact smul_left_injective _ hv.2 <| by simpa [ mul_assoc, smul_smul ] using h_sq;

/-
The sorted list of eigenvalues of a real matrix, defined as the sorted roots of its characteristic polynomial.
-/
noncomputable def sorted_eigenvalues_list {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : List ℝ :=
  (A.charpoly.roots).sort (· ≤ ·)

/-
A predicate asserting that list M interlaces list L.
-/
def interlacing (L M : List ℝ) : Prop :=
  L.length = M.length + 1 ∧
  ∀ i : Fin M.length, L[i]! ≤ M[i]! ∧ M[i]! ≤ L[i.1 + 1]!

/-
A real matrix is symmetric if and only if it is Hermitian.
-/
theorem isSymm_iff_isHermitian_real {n : Type*} [Fintype n] (A : Matrix n n ℝ) :
  A.IsSymm ↔ A.IsHermitian := by
  rw [Matrix.IsSymm, Matrix.IsHermitian, Matrix.conjTranspose, Matrix.transpose]
  simp
  rfl

/-
The sorted eigenvalues of a symmetric matrix.
-/
noncomputable def sorted_eigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) : List ℝ :=
  let hA' : A.IsHermitian := (isSymm_iff_isHermitian_real A).mp hA
  (List.ofFn (hA'.eigenvalues)).mergeSort (· ≤ ·)

/-
The number of sorted eigenvalues is n.
-/
theorem sorted_eigenvalues_length {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  (sorted_eigenvalues A hA).length = n := by
    unfold sorted_eigenvalues; aesop;

/-
For a symmetric matrix A, <Ax, y> = <x, Ay>.
-/
theorem dotProduct_mulVec_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (x y : Fin n → ℝ) :
  dotProduct (A.mulVec x) y = dotProduct x (A.mulVec y) := by
    simp +decide [ Matrix.mulVec, dotProduct, mul_comm ];
    simp +decide only [Finset.mul_sum _ _ _, mul_left_comm, mul_comm];
    rw [ Finset.sum_comm ];
    conv_rhs => rw [ ← hA ] ;
    rfl

/-
The max-min value for the k-th eigenvalue.
-/
def min_max_eigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ⨆ (C : Submodule ℝ (Fin n → ℝ)) (_ : Module.finrank ℝ C = k + 1),
    ⨅ (x : {x : C // dotProduct (x : Fin n → ℝ) (x : Fin n → ℝ) = 1}),
      dotProduct (A.mulVec (x : Fin n → ℝ)) (x : Fin n → ℝ)

/-
The sorted eigenvalues are a permutation of the eigenvalues.
-/
lemma sorted_eigenvalues_is_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  ∃ σ : Equiv.Perm (Fin n), ∀ (i : Fin n),
    (sorted_eigenvalues A hA).get ⟨i, by rw [sorted_eigenvalues_length]; exact i.2⟩ =
    Matrix.IsHermitian.eigenvalues ((isSymm_iff_isHermitian_real A).mp hA) (σ i) := by
      classical
      -- Since L and M are permutations, there is a permutation of indices matching their entries.
      have h_perm : ∀ (L M : List ℝ), List.Perm L M →
          ∃ σ : Fin L.length ≃ Fin M.length, ∀ i : Fin L.length, L.get i = M.get (σ i) := by
        intro L M h_perm
        induction h_perm with
        | nil =>
            refine ⟨Equiv.refl _, ?_⟩
            intro i
            exact (Fin.elim0 i)
        | cons a h_perm ih =>
            rename_i L' M'
            obtain ⟨σ, hσ⟩ := ih
            let f : Fin (L'.length + 1) → Fin (M'.length + 1) :=
              fun i => Fin.cases ⟨0, by simp⟩ (fun i => Fin.succ (σ i)) i
            have hf_inj : Function.Injective f := by
              intro i j hij
              cases i using Fin.cases with
              | zero =>
                  cases j using Fin.cases with
                  | zero => rfl
                  | succ j =>
                      simp [f] at hij
                      exact (Fin.succ_ne_zero _ (Eq.symm hij)).elim
              | succ i =>
                  cases j using Fin.cases with
                  | zero =>
                      simp [f] at hij
                      -- goal is closed by simp
                  | succ j =>
                      simp [f] at hij
                      exact congrArg Fin.succ hij
            have hf_surj : Function.Surjective f := by
              intro j
              cases j using Fin.cases with
              | zero =>
                  refine ⟨⟨0, by simp⟩, ?_⟩
                  simp [f]
              | succ j =>
                  refine ⟨Fin.succ (σ.symm j), ?_⟩
                  simp [f]
            let σ' : Fin (L'.length + 1) ≃ Fin (M'.length + 1) :=
              Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
            refine ⟨σ', ?_⟩
            intro i
            cases i using Fin.cases with
            | zero =>
                simp [σ', f]
            | succ i =>
                simpa [σ', f, List.get_cons_succ'] using hσ i
        | swap a b l =>
            refine ⟨Equiv.swap ⟨0, by simp⟩ ⟨1, by simp⟩, ?_⟩
            intro i
            refine Fin.cases ?h0 ?hs i
            ·
              simp
            · intro i
              refine Fin.cases ?h1 ?hrest i
              ·
                simp
              · intro j
                have hne0 : (Fin.succ (Fin.succ j) : Fin (l.length + 2)) ≠ 0 := by
                  exact Fin.succ_ne_zero _
                have hne1 : (Fin.succ (Fin.succ j) : Fin (l.length + 2)) ≠ 1 := by
                  exact Fin.succ_succ_ne_one _
                simp [Equiv.swap_apply_of_ne_of_ne hne0 hne1]
        | trans h₁ h₂ ih₁ ih₂ =>
            obtain ⟨σ₁, hσ₁⟩ := ih₁
            obtain ⟨σ₂, hσ₂⟩ := ih₂
            refine ⟨σ₁.trans σ₂, ?_⟩
            intro i
            exact (hσ₁ i).trans (hσ₂ (σ₁ i))
      generalize_proofs at *
      -- Apply the permutation property to the sorted eigenvalues and the original eigenvalues.
      obtain ⟨σ, hσ⟩ :
          ∃ σ : Fin n ≃ Fin n,
            ∀ i : Fin n,
              (sorted_eigenvalues A hA).get ⟨i, by rw [sorted_eigenvalues_length]; exact i.2⟩ =
                (Matrix.IsHermitian.eigenvalues (isSymm_iff_isHermitian_real A |>.mp hA)) (σ i) := by
        have h_perm_list :
            List.Perm (sorted_eigenvalues A hA)
              (List.ofFn (Matrix.IsHermitian.eigenvalues (isSymm_iff_isHermitian_real A |>.mp hA))) := by
          unfold sorted_eigenvalues
          generalize_proofs at *
          simpa using
            (List.mergeSort_perm
              (List.ofFn (Matrix.IsHermitian.eigenvalues (isSymm_iff_isHermitian_real A |>.mp hA)))
              (· ≤ ·))
        rcases h_perm _ _ h_perm_list with ⟨σ, hσ⟩
        let f := Matrix.IsHermitian.eigenvalues (isSymm_iff_isHermitian_real A |>.mp hA)
        have hlenL : (sorted_eigenvalues A hA).length = n := sorted_eigenvalues_length A hA
        have hlenM : (List.ofFn f).length = n := by
          simp
        -- transport σ to a permutation on Fin n using the length equalities
        let σ' : Fin n ≃ Fin n :=
          (finCongr hlenL.symm).trans (σ.trans (finCongr hlenM))
        refine ⟨σ', ?_⟩
        intro i
        let iL : Fin (sorted_eigenvalues A hA).length := finCongr hlenL.symm i
        have hidx :
            (⟨i, by
                simp [sorted_eigenvalues_length]⟩ :
              Fin (sorted_eigenvalues A hA).length) = iL := by
          apply Fin.ext
          rfl
        have hσi := hσ iL
        simpa [σ', iL, hidx, f, List.get_ofFn] using hσi
      exact ⟨σ, hσ⟩

/-
There exists an orthonormal basis of eigenvectors corresponding to the sorted eigenvalues.
-/
lemma exists_orthonormal_basis_sorted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  ∃ (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))),
    ∀ i, A.mulVec (v i) = ((sorted_eigenvalues A hA).get ⟨i, by rw [sorted_eigenvalues_length]; exact i.2⟩) • (v i) := by
      have h_eigen_decomp : ∃ (σ : Equiv.Perm (Fin n)), ∀ i : Fin n, Matrix.IsHermitian.eigenvalues ((isSymm_iff_isHermitian_real A).mp hA) (σ i) = (sorted_eigenvalues A hA).get ⟨i, by
        rw [ sorted_eigenvalues_length ] ; exact i.2⟩ := by
        have := sorted_eigenvalues_is_perm A hA
        generalize_proofs at *;
        exact ⟨ this.choose, fun i => this.choose_spec i ▸ rfl ⟩
      generalize_proofs at *;
      obtain ⟨ σ, hσ ⟩ := h_eigen_decomp
      generalize_proofs at *;
      -- By the properties of the spectral theorem, there exists an orthonormal basis of eigenvectors corresponding to the eigenvalues.
      obtain ⟨v, hv⟩ : ∃ v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), ∀ i : Fin n, A.mulVec (v i) = Matrix.IsHermitian.eigenvalues ((isSymm_iff_isHermitian_real A).mp hA) i • v i := by
        exact ⟨ Matrix.IsHermitian.eigenvectorBasis ( by tauto ), fun i => by simpa using Matrix.IsHermitian.mulVec_eigenvectorBasis ( by tauto ) i ⟩;
      refine' ⟨ v.reindex σ.symm, fun i => _ ⟩ ; aesop

/-
The inner product in EuclideanSpace is the dot product.
-/
lemma inner_eq_dotProduct {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
  inner ℝ x y = dotProduct (x : Fin n → ℝ) (y : Fin n → ℝ) := by
    simp +decide [ dotProduct, inner ];
    ac_rfl

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

/-
Equivalence between boolean functions and Fin (2^n).
-/
def boolFunEquivFin (n : ℕ) : (Fin n → Bool) ≃ Fin (2^n) :=
  (Fintype.equivFin (Fin n → Bool)).trans (finCongr (by
  norm_num [ Fintype.card_pi ]))

/-
Reindexing of Huang matrix to Fin (2^n).
-/
noncomputable def huang_matrix_fin (n : ℕ) : Matrix (Fin (2^n)) (Fin (2^n)) ℝ :=
  Matrix.reindex (boolFunEquivFin n) (boolFunEquivFin n) (huang_matrix n)

/-
The Huang matrix is symmetric.
-/
theorem huang_matrix_isSymm (n : ℕ) : (huang_matrix n).IsSymm := by
  induction' n with n ih;
  · exact rfl
  · -- By definition of huang_matrix, we know that huang_matrix (n + 1) is a block matrix with huang_matrix n on the diagonal, I on the off-diagonal, and -huang_matrix n on the other diagonal, reindexed to match the boolean hypercube indices.
    have h_block : huang_matrix (n + 1) = Matrix.reindex (finSuccEquiv_huang_custom n).symm (finSuccEquiv_huang_custom n).symm (Matrix.fromBlocks (huang_matrix n) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (-huang_matrix n)) := by
      rfl;
    simp_all +decide [ Matrix.IsSymm ];
    ext i j; simp +decide [ Matrix.fromBlocks_transpose, ih ] ;

/-
The reindexed Huang matrix is symmetric.
-/
theorem huang_matrix_fin_isSymm (n : ℕ) : (huang_matrix_fin n).IsSymm := by
  exact funext fun i => funext fun j => huang_matrix_isSymm n |>.apply _ _

/-
The square of the reindexed Huang matrix is n*I.
-/
theorem huang_matrix_fin_sq (n : ℕ) : (huang_matrix_fin n) ^ 2 = (n : ℝ) • (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℝ) := by
  ext i j;
  simp +decide [ huang_matrix_fin, sq ];
  convert congr_fun ( congr_fun ( huang_matrix_sq n ) ( ( boolFunEquivFin n ).symm i ) ) ( ( boolFunEquivFin n ).symm j ) using 1 ; norm_num [ Matrix.mul_apply ];
  · rw [ sq, Matrix.mul_apply ];
  · simp +decide [ Matrix.one_apply, Matrix.smul_apply ]

/-
The trace of the Huang matrix is 0.
-/
theorem huang_matrix_trace (n : ℕ) : Matrix.trace (huang_matrix n) = 0 := by
  induction n <;> simp_all +decide [ Matrix.trace ];
  · rfl;
  · rename_i n ih; rw [ show ( huang_matrix ( n + 1 ) ) = Matrix.reindex ( finSuccEquiv_huang_custom n ).symm ( finSuccEquiv_huang_custom n ).symm ( Matrix.fromBlocks ( huang_matrix n ) ( 1 : Matrix _ _ ℝ ) ( 1 : Matrix _ _ ℝ ) ( -huang_matrix n ) ) by rfl ] ; simp +decide ;
    unfold finSuccEquiv_huang_custom;
    unfold finSuccEquiv_custom boolProdEquivSum_custom; simp +decide [ Matrix.fromBlocks ] ;
    rw [ show ( Finset.univ : Finset ( Fin ( n + 1 ) → Bool ) ) = Finset.image ( fun x : Fin n → Bool => Fin.cons true x ) Finset.univ ∪ Finset.image ( fun x : Fin n → Bool => Fin.cons false x ) Finset.univ from ?_, Finset.sum_union ] <;> norm_num [ Finset.sum_image, ih ];
    · rw [ neg_add_eq_zero ];
      exact rfl
    · norm_num [ Finset.disjoint_left ];
    · ext x; simp +decide ;
      exact if h : x 0 then Or.inl ⟨ fun i => x i.succ, by ext i; cases i using Fin.inductionOn <;> aesop ⟩ else Or.inr ⟨ fun i => x i.succ, by ext i; cases i using Fin.inductionOn <;> aesop ⟩

/-
Every eigenvalue of the Huang matrix squares to n.
-/
theorem huang_eigenvalues_sq_eq_n (n : ℕ) (i : Fin (2^n)) :
  ((sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)).get ⟨i, by rw [sorted_eigenvalues_length]; exact i.2⟩) ^ 2 = n := by
    -- Apply the fact that the eigenvalues of the Huang matrix square to n.
    have h_eigenvalue : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (huang_matrix_fin n)) μ → μ ^ 2 = n := by
      intro μ hμ
      generalize_proofs at *;
      have h_eigenvalue : μ ^ 2 = n := by
        have h_sq : (huang_matrix_fin n) ^ 2 = (n : ℝ) • (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℝ) := by
          exact huang_matrix_fin_sq n
        have h_eigenvalue : ∀ (v : Fin (2^n) → ℝ), v ≠ 0 → (huang_matrix_fin n).mulVec v = μ • v → μ ^ 2 = n := by
          intros v hv hμv
          have h_eigenvalue : (huang_matrix_fin n).mulVec ((huang_matrix_fin n).mulVec v) = μ ^ 2 • v := by
            rw [ hμv, Matrix.mulVec_smul, pow_two, MulAction.mul_smul ];
            rw [ hμv ]
          generalize_proofs at *;
          have h_eigenvalue : (huang_matrix_fin n).mulVec ((huang_matrix_fin n).mulVec v) = (n : ℝ) • v := by
            simp +decide [ ← sq, h_sq ];
            simp +decide [ Matrix.smul_eq_diagonal_mul ]
          generalize_proofs at *;
          exact smul_left_injective _ hv <| by aesop;
        generalize_proofs at *;
        obtain ⟨ v, hv ⟩ := hμ.exists_hasEigenvector;
        cases hv ; aesop
      generalize_proofs at *;
      exact h_eigenvalue
    generalize_proofs at *;
    -- By definition of sorted_eigenvalues, every element in the list is an eigenvalue of the matrix.
    have h_sorted_eigenvalue : ∀ μ ∈ sorted_eigenvalues (huang_matrix_fin n) ‹_›, Module.End.HasEigenvalue (Matrix.toLin' (huang_matrix_fin n)) μ := by
      unfold sorted_eigenvalues;
      simp_all +decide [ Module.End.HasUnifEigenvalue ];
      intro a; specialize h_eigenvalue ( Matrix.IsHermitian.eigenvalues ‹_› a ) ; simp_all +decide [ Submodule.eq_bot_iff ] ;
      have := Matrix.IsHermitian.eigenvectorBasis ‹_› |> OrthonormalBasis.orthonormal;
      exact ⟨ _, Matrix.IsHermitian.mulVec_eigenvectorBasis _ _, this.linearIndependent.ne_zero _ ⟩;
    aesop

/-
The sum of sorted eigenvalues is the trace.
-/
theorem sum_sorted_eigenvalues_eq_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  (sorted_eigenvalues A hA).sum = A.trace := by
    -- The sum of the eigenvalues of a symmetric matrix is equal to its trace.
    have h_sum_eigenvalues : (List.ofFn (Matrix.IsHermitian.eigenvalues ((isSymm_iff_isHermitian_real A).mp hA))).sum = Matrix.trace A := by
      -- Apply the theorem that states the trace of a matrix is equal to the sum of its eigenvalues.
      have h_trace_eq_sum_eigenvalues : Matrix.trace A = ∑ i : Fin n, (Matrix.IsHermitian.eigenvalues (isSymm_iff_isHermitian_real A |>.mp hA)) i := by
        have := ( isSymm_iff_isHermitian_real A ).mp hA;
        have := this.trace_eq_sum_eigenvalues;
        exact_mod_cast this;
      rw [ h_trace_eq_sum_eigenvalues, List.sum_ofFn ];
    rw [ ← h_sum_eigenvalues ];
    unfold sorted_eigenvalues;
    rw [ List.Perm.sum_eq ( List.mergeSort_perm _ _ ) ]

/-
If a list contains only c and -c and sums to 0, then the counts are equal.
-/
lemma list_sum_zero_eq_count {c : ℝ} (hc : c ≠ 0) (L : List ℝ)
  (h_mem : ∀ x ∈ L, x = c ∨ x = -c) (h_sum : L.sum = 0) :
  L.count c = L.count (-c) := by
    -- We can split the sum into the sum of the c's and the sum of the -c's.
    have h_split_sum : ∑ x ∈ L.toFinset, x * (L.count x) = c * (L.count c) + (-c) * (L.count (-c)) := by
      field_simp;
      rw [ Finset.sum_eq_add ( c ) ( -c ) ] <;> norm_num;
      · ring;
      · exact fun h => hc <| by linarith;
      · grind;
      · exact fun h => Or.inr <| List.count_eq_zero_of_not_mem h;
      · exact fun h => Or.inr <| List.count_eq_zero_of_not_mem h;
    have h_split_sum_eq_zero : ∑ x ∈ L.toFinset, x * (L.count x) = L.sum := by
      simp +decide [ Finset.sum_list_count ];
      ac_rfl;
    exact_mod_cast ( mul_left_cancel₀ hc <| by linarith : ( L.count c : ℝ ) = L.count ( -c ) )

/-
A list of -c's followed by c's is sorted if c ≥ 0.
-/
lemma sorted_replicate_append_replicate {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
  (List.replicate m (-c) ++ List.replicate m c).Sorted (· ≤ ·) := by
    -- The list is sorted because each element in the first part is -c and each element in the second part is c, and -c ≤ c since c ≥ 0.
    simp [List.Sorted];
    rw [ List.pairwise_append ] ; aesop

/-
If a sorted list has m -c's and m c's, it is equal to m -c's followed by m c's.
-/
lemma list_eq_replicate_append_replicate {c : ℝ} (hc : 0 ≤ c) (L : List ℝ) (m : ℕ)
  (h_len : L.length = 2 * m)
  (h_count_neg : L.count (-c) = m)
  (h_count_pos : L.count c = m)
  (h_mem : ∀ x ∈ L, x = c ∨ x = -c)
  (h_sorted : L.Sorted (· ≤ ·)) :
  L = List.replicate m (-c) ++ List.replicate m c := by
    refine' List.eq_of_perm_of_sorted _ h_sorted ( sorted_replicate_append_replicate hc m );
    rw [ List.perm_iff_count ];
    intro a; by_cases ha : a = c <;> by_cases ha' : a = -c <;> simp_all +decide [ List.count_replicate ] ;
    · cases m <;> simp_all +decide [ neg_eq_iff_add_eq_zero ];
      rw [ List.eq_replicate_of_mem h_mem ] at h_count_pos ; aesop;
    · aesop;
    · exact fun h => False.elim <| ha <| by linarith;
    · rw [ List.count_eq_zero_of_not_mem fun h => by cases h_mem a h <;> tauto ] ; aesop

/-
If a list contains only c and d, their counts sum to the length.
-/
lemma list_count_add_count_eq_length {α : Type*} [DecidableEq α] {c d : α} (hcd : c ≠ d) (L : List α)
  (h_mem : ∀ x ∈ L, x = c ∨ x = d) :
  L.count c + L.count d = L.length := by
    induction' L with x xs ih;
    · rfl;
    · cases h_mem x ( by simp +decide ) <;> simp_all +decide [ List.count_cons ];
      · linarith;
      · grind

/-
Trace is invariant under reindexing.
-/
theorem trace_reindex_eq_trace {n : Type*} [Fintype n] {m : Type*} [Fintype m] [DecidableEq n] [DecidableEq m]
  (e : n ≃ m) (A : Matrix n n ℝ) :
  Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
    simp +decide [ Matrix.trace ];
    conv_rhs => rw [ ← Equiv.sum_comp e.symm ] ;

/-
The trace of the reindexed Huang matrix is 0.
-/
theorem huang_matrix_fin_trace (n : ℕ) : Matrix.trace (huang_matrix_fin n) = 0 := by
  -- The trace of the reindexed matrix is the same as the original matrix, which is 0 by huang_matrix_trace. Hence, we can conclude.
  have h_trace_reindex : Matrix.trace (Matrix.reindex (boolFunEquivFin n) (boolFunEquivFin n) (huang_matrix n)) = Matrix.trace (huang_matrix n) := by
    exact trace_reindex_eq_trace (boolFunEquivFin n) (huang_matrix n)
  exact h_trace_reindex.trans ( huang_matrix_trace n )

/-
sorted_eigenvalues returns a sorted list.
-/
theorem sorted_eigenvalues_sorted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  (sorted_eigenvalues A hA).Sorted (· ≤ ·) := by
    unfold sorted_eigenvalues;
    exact
      List.sorted_mergeSort' (fun x1 x2 => x1 ≤ x2)
        (List.ofFn (sorted_eigenvalues._proof_1 A hA).eigenvalues)

/-
Accessing an element in a list of two concatenated replicated lists.
-/
lemma list_replicate_append_replicate_get {n : ℕ} {c : ℝ} (i : Fin (2 * n)) :
  (List.replicate n (-c) ++ List.replicate n c).get ⟨i, by
    simpa [ two_mul ] using i.2⟩ = if i < n then -c else c := by
    aesop

/-
A sorted list of length 2m with elements squaring to c^2 and sum 0 is m -c's then m c's.
-/
lemma sorted_list_of_sq_eq_and_sum_zero {L : List ℝ} {c : ℝ} {m : ℕ} (hc : 0 < c)
  (h_len : L.length = 2 * m)
  (h_sq : ∀ x ∈ L, x^2 = c^2)
  (h_sum : L.sum = 0)
  (h_sorted : L.Sorted (· ≤ ·)) :
  L = List.replicate m (-c) ++ List.replicate m c := by
    -- Since every element in L is either c or -c and their sum is zero, the counts of c and -c must be equal.
    have h_count_eq : L.count c = L.count (-c) := by
      apply_rules [ list_sum_zero_eq_count ];
      · positivity;
      · exact fun x hx => eq_or_eq_neg_of_sq_eq_sq _ _ <| h_sq x hx;
    -- Since the counts of $c$ and $-c$ are equal and their sum is zero, the number of $c$'s and $-c$'s must be $m$ each.
    have h_count_m : L.count c = m ∧ L.count (-c) = m := by
      have h_count_eq : L.count c + L.count (-c) = 2 * m := by
        rw [ ← h_len, List.length_eq_countP_add_countP ];
        congr;
        rw [ List.countP_congr ] ; aesop;
        grind;
      grind;
    apply list_eq_replicate_append_replicate hc.le L m h_len;
    · exact h_count_m.2;
    · exact h_count_m.1;
    · exact fun x hx => eq_or_eq_neg_of_sq_eq_sq _ _ <| h_sq x hx;
    · assumption

/-
If a list satisfies the properties, its elements are determined.
-/
lemma list_properties_to_values {L : List ℝ} {c : ℝ} {m : ℕ} (hc : 0 < c)
  (h_len : L.length = 2 * m)
  (h_sq : ∀ x ∈ L, x^2 = c^2)
  (h_sum : L.sum = 0)
  (h_sorted : L.Sorted (· ≤ ·))
  (i : Fin (2 * m)) :
  L.get ⟨i, by rw [h_len]; exact i.2⟩ = if (i : ℕ) < m then -c else c := by
    have h_eq_replicate_append_replicate : L = List.replicate m (-c) ++ List.replicate m c := by
      exact sorted_list_of_sq_eq_and_sum_zero hc h_len h_sq h_sum h_sorted
    generalize_proofs at *; aesop;

/-
The sorted eigenvalues of A_{n+1} are 2^n copies of -sqrt(n+1) followed by 2^n copies of sqrt(n+1).
-/
lemma huang_eigenvalues_eq_list_succ (n : ℕ) :
  let evs := sorted_eigenvalues (huang_matrix_fin (n + 1)) (huang_matrix_fin_isSymm (n + 1))
  evs = List.replicate (2^n) (-Real.sqrt (n + 1)) ++ List.replicate (2^n) (Real.sqrt (n + 1)) := by
    generalize_proofs at *;
    apply sorted_list_of_sq_eq_and_sum_zero;
    · positivity;
    · rw [ sorted_eigenvalues_length ] ; norm_num [ pow_succ' ];
    · intro x hx;
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hx;
      have := huang_eigenvalues_sq_eq_n ( n + 1 ) ⟨ i, by
        refine' i.2.trans_le _;
        rw [ sorted_eigenvalues_length ] ⟩
      generalize_proofs at *;
      rw [ Real.sq_sqrt <| by positivity ] ; aesop;
    · rw [ sum_sorted_eigenvalues_eq_trace, huang_matrix_fin_trace ];
    · exact (by
        expose_names
        exact sorted_eigenvalues_sorted (huang_matrix_fin (n + 1)) pf)

/-
The sorted eigenvalues of the Huang matrix.
-/
noncomputable def huang_eigenvalues (n : ℕ) : List ℝ :=
  sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)

/-
The absolute value of the Huang matrix entries is the adjacency matrix of the hypercube.
-/
theorem abs_huang_eq_adjacency (n : ℕ) (i j : Fin n → Bool) :
  |huang_matrix n i j| = if (Finset.filter (fun k => i k ≠ j k) Finset.univ).card = 1 then 1 else 0 := by
    rcases n with ( _ | n );
    · aesop;
    · -- By induction on $n$, we can show that the absolute value of the entries of the Huang matrix is the adjacency matrix of the hypercube.
      have h_ind : ∀ n : ℕ, ∀ i j : Fin (n + 1) → Bool, |(huang_matrix (n + 1)) i j| = if (Finset.card (Finset.filter (fun k => i k ≠ j k) Finset.univ)) = 1 then 1 else 0 := by
        -- We proceed by induction on $n$.
        intro n
        induction' n with n ih;
        · simp +decide [ huang_matrix ];
          intro i j; fin_cases i <;> fin_cases j <;> simp +decide [ finSuccEquiv_huang_custom ] ;
          · rfl;
          · simp +decide [ boolProdEquivSum_custom, finSuccEquiv_custom ];
            simp +decide [ Matrix.one_apply ];
          · simp +decide [ boolProdEquivSum_custom, finSuccEquiv_custom ];
            simp +decide [ Matrix.one_apply ];
          · rfl;
        · intro i j;
          -- By definition of `huang_matrix`, we can split into cases based on whether `i` and `j` are in the same block or different blocks.
          have h_split : ∀ i j : Fin (n + 2) → Bool, |(huang_matrix (n + 2)) i j| = if (i 0 = j 0) then |(huang_matrix (n + 1)) (fun k => i (Fin.succ k)) (fun k => j (Fin.succ k))| else if (Finset.card (Finset.filter (fun k => i (Fin.succ k) ≠ j (Fin.succ k)) Finset.univ)) = 0 then 1 else 0 := by
            intros i j;
            have h_split : ∀ i j : Fin (n + 2) → Bool, |(huang_matrix (n + 2)) i j| = if (i 0 = j 0) then |(huang_matrix (n + 1)) (fun k => i (Fin.succ k)) (fun k => j (Fin.succ k))| else if (Finset.card (Finset.filter (fun k => i (Fin.succ k) ≠ j (Fin.succ k)) Finset.univ)) = 0 then 1 else 0 := by
              intro i j
              have h_def : huang_matrix (n + 2) = Matrix.reindex (finSuccEquiv_huang_custom (n + 1)).symm (finSuccEquiv_huang_custom (n + 1)).symm (Matrix.fromBlocks (huang_matrix (n + 1)) (1 : Matrix _ _ ℝ) (1 : Matrix _ _ ℝ) (-huang_matrix (n + 1))) := by
                exact rfl
              simp +decide [ h_def, Matrix.fromBlocks ];
              unfold finSuccEquiv_huang_custom;
              unfold finSuccEquiv_custom; simp +decide ;
              unfold boolProdEquivSum_custom; simp +decide ;
              split_ifs <;> simp +decide [ *, Matrix.one_apply ];
              all_goals simp_all +decide [ funext_iff ];
            exact h_split i j;
          rw [ show ( Finset.univ.filter fun k => i k ≠ j k ) = if i 0 = j 0 then Finset.image ( Fin.succ ) ( Finset.univ.filter fun k => i ( Fin.succ k ) ≠ j ( Fin.succ k ) ) else Finset.image ( Fin.succ ) ( Finset.univ.filter fun k => i ( Fin.succ k ) ≠ j ( Fin.succ k ) ) ∪ { 0 } from ?_ ];
          · split_ifs <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
          · ext ( _ | k ) <;> simp +decide;
            · split_ifs <;> simp +decide [ * ];
            · split_ifs <;> simp_all +decide [ Finset.mem_image, Finset.mem_insert ];
              · exact ⟨ fun h => ⟨ ⟨ k, by linarith ⟩, h, rfl ⟩, by rintro ⟨ a, ha, ha' ⟩ ; cases a ; aesop ⟩;
              · exact ⟨ fun h => ⟨ ⟨ k, by linarith ⟩, h, rfl ⟩, by rintro ⟨ a, h, ha ⟩ ; cases a ; aesop ⟩;
      exact h_ind n i j

/-
The sorted eigenvalues of the Huang matrix A_n (for n > 0) are 2^(n-1) copies of -sqrt(n) and 2^(n-1) copies of sqrt(n).
-/
theorem huang_eigenvalues_eq_list (n : ℕ) (hn : n ≠ 0) :
  let evs := sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)
  evs = List.replicate (2^(n-1)) (-Real.sqrt n) ++ List.replicate (2^(n-1)) (Real.sqrt n) := by
    induction' n with n ih;
    · contradiction;
    · convert huang_eigenvalues_eq_list_succ n using 1;
      norm_cast

/-
Any eigenvalue of a real matrix is bounded in absolute value by the maximum absolute row sum.
-/
theorem eigenvalue_le_max_row_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
  (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
  ∃ i : Fin n, |μ| ≤ Finset.sum Finset.univ (fun j => |A i j|) := by
    -- Let v be a nonzero eigenvector. Let i be the index maximizing |v_i|.
    obtain ⟨v, hv⟩ : ∃ v : Fin n → ℝ, v ≠ 0 ∧ A.mulVec v = μ • v := by
      obtain ⟨ v, hv ⟩ := hμ.exists_hasEigenvector;
      cases hv ; aesop
    obtain ⟨i, hi⟩ : ∃ i : Fin n, ∀ j : Fin n, |v j| ≤ |v i| := by
      have := Finset.exists_max_image Finset.univ ( fun i => |v i| ) ⟨ ⟨ 0, Nat.pos_of_ne_zero ( by aesop_cat ) ⟩, Finset.mem_univ _ ⟩ ; aesop;
    -- Then |μ v_i| = |(Av)_i| = |sum_j A_ij v_j| ≤ sum_j |A_ij| |v_j| ≤ sum_j |A_ij| |v_i| = |v_i| sum_j |A_ij|.
    have h_bound : |μ * v i| ≤ |v i| * ∑ j, |A i j| := by
      have h_bound : |μ * v i| = |∑ j, A i j * v j| := by
        have := congr_fun hv.2 i; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
      rw [ h_bound, Finset.mul_sum _ _ _ ];
      exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun j _ => by rw [ abs_mul, mul_comm ] ; exact mul_le_mul_of_nonneg_right ( hi j ) ( abs_nonneg _ ) );
    exact ⟨ i, by
      rw [ abs_mul ] at h_bound
      refine le_of_not_gt ?_
      intro hi'
      have hvipos : 0 < |v i| := by
        apply abs_pos.mpr
        intro hi''
        exact hv.1 <| funext fun j => by simpa [ hi'' ] using hi j
      have hgtmul : |μ| * |v i| > |v i| * ∑ j, |A i j| := by
        nlinarith [hi', hvipos]
      exact (not_le_of_gt hgtmul) h_bound ⟩

/-
Checking Fintype.card_coe
-/
/-
The largest eigenvalue of a symmetric matrix is bounded by the maximum degree of the graph defined by its non-zero entries.
-/
theorem spectral_radius_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (G : SimpleGraph (Fin n))
  (h_adj : ∀ i j, |A i j| ≤ if G.Adj i j then 1 else 0) (hn : n ≠ 0) :
  let evs := sorted_eigenvalues A hA
  let lambda_max := evs.getLast (List.ne_nil_of_length_pos (by rw [sorted_eigenvalues_length A hA]; exact Nat.pos_of_ne_zero hn))
  lambda_max ≤ G.maxDegree := by
    -- Since the largest eigenvalue is bounded by the maximum degree of the graph (from Lemma~\ref{lem:eigenvalue_le_max_row_sum}), we have:
    have h_bound : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ ≤ G.maxDegree := by
      intro μ hμ
      obtain ⟨i, hi⟩ := eigenvalue_le_max_row_sum A μ hμ;
      -- Since $|A i j| \leq 1$ if $G.Adj i j$ and $0$ otherwise, we have $\sum j, |A i j| \leq \sum j in G.neighborFinset i, 1$.
      have h_sum_le_neighbor : ∑ j, |A i j| ≤ ∑ j ∈ G.neighborFinset i, 1 := by
        exact le_trans ( Finset.sum_le_sum fun _ _ => h_adj _ _ ) ( by simp +decide [ SimpleGraph.neighborFinset_def ] );
      exact le_trans ( le_abs_self μ ) ( hi.trans <| h_sum_le_neighbor.trans <| mod_cast by simpa using G.degree_le_maxDegree i );
    have h_sorted : ∀ μ ∈ sorted_eigenvalues A hA, μ ≤ G.maxDegree := by
      intros μ hμ
      obtain ⟨i, hi⟩ : ∃ i : Fin n, μ = Matrix.IsHermitian.eigenvalues ((isSymm_iff_isHermitian_real A).mp hA) i := by
        unfold sorted_eigenvalues at hμ; aesop;
      convert h_bound μ ?_;
      have := ( Matrix.IsHermitian.eigenvalues_eq hA );
      simp_all +decide [ Module.End.HasUnifEigenvalue ];
      simp_all +decide [ Submodule.eq_bot_iff ];
      exact ⟨ _, by simpa [ this ] using Matrix.IsHermitian.mulVec_eigenvectorBasis hA i, by simpa [ this ] using ( Matrix.IsHermitian.eigenvectorBasis hA ).orthonormal.ne_zero i ⟩;
    exact h_sorted _ <| List.getLast_mem _

/-
The Rayleigh quotient of a vector x with respect to a matrix A is <x, Ax> / <x, x>.
-/
def rayleigh_quotient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (A.mulVec x) / dotProduct x x

/-
The Courant-Fischer Min-Max value (Inf-Sup) for the k-th eigenvalue.
-/
def courant_fischer_inf_sup {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : ℝ :=
  ⨅ (V : Submodule ℝ (Fin n → ℝ)) (_ : Module.finrank ℝ V = k + 1),
    ⨆ (x : {x : V // x.1 ≠ 0}), rayleigh_quotient A x.1

/-
The Rayleigh quotient is invariant under reindexing.
-/
lemma rayleigh_quotient_reindex {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin n ≃ Fin m) (x : Fin n → ℝ) :
  rayleigh_quotient A x = rayleigh_quotient (Matrix.reindex e e A) (x ∘ e.symm) := by
    unfold rayleigh_quotient;
    simp +decide [ Matrix.mulVec, dotProduct ];
    simp +decide only [← Equiv.sum_comp e];
    simp +decide

/-
The Rayleigh quotient of a zero-padded vector is equal to the Rayleigh quotient of the original vector with respect to the submatrix.
-/
lemma rayleigh_quotient_submatrix_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
  (equiv : {x // x ∈ S} ≃ Fin S.card)
  (y : Fin S.card → ℝ) :
  let x : Fin n → ℝ := fun i => if h : i ∈ S then y (equiv ⟨i, h⟩) else 0
  rayleigh_quotient A x = rayleigh_quotient (Matrix.reindex equiv equiv (A.submatrix Subtype.val Subtype.val)) y := by
    -- By definition of $x$, we can split the sum into two parts: one over $S$ and one over the complement of $S$.
    simp [rayleigh_quotient];
    congr 1;
    · simp +decide [ dotProduct, Matrix.mulVec ];
      -- By reindexing the sums using the equivalence `equiv`, we can show that the two expressions are equal.
      have h_reindex : ∑ x : Fin n, (if h : x ∈ S then y (equiv ⟨x, h⟩) * ∑ x_1 : Fin n, (if h : x_1 ∈ S then A x x_1 * y (equiv ⟨x_1, h⟩) else 0) else 0) = ∑ x : S, y (equiv x) * ∑ x_1 : S, A x x_1 * y (equiv x_1) := by
        rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
        · rw [ ← Finset.sum_coe_sort ];
          simp +decide;
          refine' Finset.sum_congr rfl fun x hx => congr_arg _ _;
          rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
          · refine' Finset.sum_bij ( fun x hx => ⟨ x, by aesop ⟩ ) _ _ _ _ <;> aesop;
          · aesop;
        · aesop;
      convert h_reindex using 1;
      conv_rhs => rw [ ← Equiv.sum_comp equiv.symm ] ;
      refine' Finset.sum_congr rfl fun i hi => _;
      rw [ ← Equiv.sum_comp equiv ] ; aesop;
    · simp +decide [ dotProduct ];
      rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
      · rw [ ← Finset.sum_attach ];
        rw [ ← Equiv.sum_comp equiv ] ; aesop;
      · aesop

/-
If a vector lies in the span of the eigenvectors corresponding to eigenvalues $\ge \alpha_k$, its Rayleigh quotient is at least $\alpha_k$.
-/
lemma rayleigh_ge_of_mem_span_top {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (k : Fin n)
  (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
  (hv : ∀ i, A.mulVec (v i) = ((sorted_eigenvalues A hA).get ⟨i, by rw [sorted_eigenvalues_length]; exact i.isLt⟩) • (v i))
  (x : EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Submodule.span ℝ (Set.range (fun i : {j : Fin n // k ≤ j} => v i)))
  (hx0 : x ≠ 0) :
  rayleigh_quotient A x ≥ (sorted_eigenvalues A hA).get ⟨k, by rw [sorted_eigenvalues_length]; exact k.isLt⟩ := by
    classical
    set ev := sorted_eigenvalues A hA
    have hv' : ∀ i, A.mulVec (v i) = (ev.get ⟨i, by simp [ev, sorted_eigenvalues_length]⟩) • v i := by
      simpa [ev] using hv
    -- Let $x = \sum_{i \in K} c_i v_i$ be the decomposition of $x$ in the orthonormal basis $v$.
    obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, x = ∑ i : Fin n, c i • v i ∧ ∀ i : Fin n, i < k → c i = 0 := by
      -- By definition of submodule span, there exists a finite subset of the basis vectors that spans x.
      obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, x = ∑ i : Fin n, c i • v i ∧ ∀ i : Fin n, i < k → c i = 0 := by
        have h_span : x ∈ Submodule.span ℝ (Set.range (fun i : Fin n => if i < k then 0 else v i)) := by
          refine' Submodule.span_le.mpr _ hx;
          rintro _ ⟨ i, rfl ⟩ ; by_cases hi : ( i : Fin n ) < k <;> simp +decide;
          · exfalso; exact (not_le_of_gt hi) i.2;
          · exact Submodule.subset_span ⟨ i, by aesop ⟩
        rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_span;
        obtain ⟨ c, hc ⟩ := h_span; use fun i => if i < k then 0 else c i; simp_all +decide [ Finsupp.sum_fintype ] ;
      use c;
    -- Since $v$ is an orthonormal basis, we have $\|x\|^2 = \sum_{i=0}^{n-1} c_i^2$ and $\langle x, Ax \rangle = \sum_{i=0}^{n-1} c_i^2 \lambda_i$.
    have h_norm : dotProduct x x = ∑ i : Fin n, c i ^ 2 := by
      simp +decide [ hc.1, dotProduct, sq ];
      have h_norm : ∀ i j : Fin n, dotProduct (v i) (v j) = if i = j then 1 else 0 := by
        intro i j; specialize hv' i; replace hv' := congr_arg ( fun x => dotProduct x ( v j ) ) hv'; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
        have := v.orthonormal; simp_all +decide [ orthonormal_iff_ite ] ;
        simpa [ mul_comm, inner ] using this i j
      generalize_proofs at *;
      -- By expanding the dot product and using the orthonormality of the basis vectors, we can simplify the expression.
      have h_expand : ∀ x y : Fin n → ℝ, (∑ i, x i • v i) ⬝ᵥ (∑ j, y j • v j) = ∑ i, x i * y i := by
        simp +decide [ dotProduct, Finset.mul_sum _ _ _, mul_comm, mul_left_comm ];
        simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_comm ];
        simp_all +decide [ dotProduct ]
      generalize_proofs at *;
      convert h_expand c c using 1
    have h_inner : dotProduct x (A.mulVec x) = ∑ i : Fin n, c i ^ 2 * ev.get ⟨i, by
      simp [ev, sorted_eigenvalues_length]⟩ := by
      -- By linearity of the inner product and the fact that $A.mulVec$ is linear, we can distribute the inner product over the sum.
      have h_inner_dist : dotProduct (∑ i, c i • v i) (A.mulVec (∑ j, c j • v j)) = ∑ i, ∑ j, c i * c j * dotProduct (v i) (A.mulVec (v j)) := by
        simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, Finset.sum_mul ];
        simp +decide only [← Finset.sum_product'];
        apply Finset.sum_bij (fun x _ => (x.2.2.2, x.2.2.1, x.1, x.2.1));
        · simp +decide;
        · aesop;
        · simp +zetaDelta at *;
        · simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
      -- Since $v$ is an orthonormal basis, we have $\langle v_i, v_j \rangle = \delta_{ij}$.
      have h_orthonormal : ∀ i j, dotProduct (v i) (v j) = if i = j then 1 else 0 := by
        intro i j; have := v.orthonormal; simp_all +decide [ orthonormal_iff_ite ] ;
        convert this i j using 1;
        simp +decide [ dotProduct, inner ];
        ac_rfl
      generalize_proofs at *;
      simp_all +decide [ pow_two, mul_assoc ];
      simp +decide [ dotProduct, Finset.mul_sum _ _ _, mul_left_comm ];
      simp_all +decide [ ← Finset.mul_sum _ _ _, dotProduct ];
      simp [ev]
    generalize_proofs at *;
    -- Since $v$ is an orthonormal basis, we have $\lambda_i \geq \alpha_k$ for all $i \geq k$.
    have h_lambda_ge_alpha : ∀ i : Fin n, k ≤ i → ev.get ⟨i, by
      simp [ev, sorted_eigenvalues_length]⟩ ≥ ev.get ⟨k, by
      simp [ev, sorted_eigenvalues_length]⟩ := by
      intros i hi
      have h_sorted : ev.get ⟨i, by
        simp [ev, sorted_eigenvalues_length]⟩ ≥ ev.get ⟨k, by
        simp [ev, sorted_eigenvalues_length]⟩ := by
        have h_sorted_list : List.Sorted (· ≤ ·) ev := by
          simpa [ev] using sorted_eigenvalues_sorted A hA
        have := List.pairwise_iff_get.mp h_sorted_list;
        grind
      generalize_proofs at *;
      exact h_sorted
    generalize_proofs at *;
    -- Since $v$ is an orthonormal basis, we have $\sum_{i=0}^{n-1} c_i^2 \lambda_i \geq \alpha_k \sum_{i=0}^{n-1} c_i^2$.
    have h_sum_ge_alpha : ∑ i : Fin n, c i ^ 2 * ev.get ⟨i, by
      simp [ev, sorted_eigenvalues_length]⟩ ≥ ev.get ⟨k, by
      simp [ev, sorted_eigenvalues_length]⟩ * ∑ i : Fin n, c i ^ 2 := by
      rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i _ => by cases le_or_gt k i <;> [ exact by nlinarith only [ h_lambda_ge_alpha i ‹_› ] ; ; exact by rw [ hc.2 i ‹_› ] ; nlinarith only [ h_lambda_ge_alpha k le_rfl ] ] ;
    generalize_proofs at *;
    field_simp;
    rw [ rayleigh_quotient ];
    rw [ h_inner, h_norm, le_div_iff₀ ];
    · exact h_sum_ge_alpha;
    · exact h_norm ▸ lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ) ( Ne.symm <| by intro H; exact hx0 <| by ext i; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] )

/-
The k-th eigenvalue is less than or equal to the supremum of the Rayleigh quotient over any (k+1)-dimensional subspace.
-/
lemma le_sup_rayleigh_of_dim_eq_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (k : Fin n)
  (V : Submodule ℝ (Fin n → ℝ))
  (hV : Module.finrank ℝ V = k + 1) :
  (sorted_eigenvalues A hA).get ⟨k, by rw [sorted_eigenvalues_length]; exact k.isLt⟩ ≤ ⨆ (x : {x : V // x.1 ≠ 0}), rayleigh_quotient A x.1 := by
    -- Let U be the span of eigenvectors v_k, ..., v_{n-1}.
    set U : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ (Set.range (fun i : {j : Fin n // k ≤ j} => (Classical.choose (exists_orthonormal_basis_sorted A hA)) i));
    -- Since $V$ is $k+1$-dimensional and $U$ is $n-k$-dimensional, their intersection $U \cap V$ has dimension at least $1$.
    have h_inter : Module.finrank ℝ (↥(U ⊓ V)) ≥ 1 := by
      have h_inter : Module.finrank ℝ U = n - k := by
        rw [ @finrank_span_eq_card ];
        · rw [ Fintype.card_subtype ];
          rw [ show ( Finset.univ.filter fun x : Fin n => k ≤ x ) = Finset.Ici k by ext; simp +decide ] ; simp +decide;
        · refine' LinearIndependent.comp _ _ _;
          · exact ( Classical.choose ( exists_orthonormal_basis_sorted A hA ) ).orthonormal.linearIndependent;
          · exact Subtype.coe_injective;
      have h_inter : Module.finrank ℝ (↥(U ⊔ V)) ≤ n := by
        exact le_trans ( Submodule.finrank_le _ ) ( by simp );
      have := Submodule.finrank_sup_add_finrank_inf_eq U V;
      linarith [ Nat.sub_add_cancel ( show ( k : ℕ ) ≤ n from k.2.le ) ];
    -- Let $x$ be a nonzero vector in $U \cap V$.
    obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, x ≠ 0 ∧ x ∈ U ⊓ V := by
      contrapose! h_inter;
      rw [ show U ⊓ V = ⊥ from eq_bot_iff.mpr fun x hx => Classical.not_not.1 fun hx' => h_inter x hx' hx ] ; norm_num;
    refine' le_trans _ ( le_ciSup _ ⟨ ⟨ x, by aesop ⟩, by aesop ⟩ );
    · apply rayleigh_ge_of_mem_span_top A hA k (Classical.choose (exists_orthonormal_basis_sorted A hA)) (Classical.choose_spec (exists_orthonormal_basis_sorted A hA)) x;
      · exact hx.2.1;
      · exact hx.1;
    · refine' ⟨ ∑ i, ∑ j, |A i j|, Set.forall_mem_range.2 fun x => _ ⟩;
      refine' div_le_of_le_mul₀ _ _ _;
      · exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _;
      · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _;
      · -- By the properties of the dot product and the triangle inequality, we can bound the expression.
        have h_dot_product : ∀ (x : Fin n → ℝ), x ≠ 0 → |dotProduct x (A.mulVec x)| ≤ (∑ i, ∑ j, |A i j|) * dotProduct x x := by
          intros x hx_nonzero
          have h_dot_product : |dotProduct x (A.mulVec x)| ≤ ∑ i, ∑ j, |A i j| * |x i| * |x j| := by
            simp +decide [ dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_comm, mul_left_comm ];
            exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun j _ => by rw [ abs_mul, abs_mul ] );
          refine le_trans h_dot_product ?_;
          norm_num [ Finset.sum_mul _ _ _, mul_assoc, dotProduct ];
          exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ( by nlinarith only [ abs_mul_abs_self ( x i ), abs_mul_abs_self ( x j ), Finset.single_le_sum ( fun i _ => mul_self_nonneg ( x i ) ) ( Finset.mem_univ i ), Finset.single_le_sum ( fun i _ => mul_self_nonneg ( x i ) ) ( Finset.mem_univ j ) ] ) ( abs_nonneg _ );
        exact le_of_abs_le ( h_dot_product _ x.2 )

/-
The intersection of a subspace of dimension n-k and a subspace of dimension k+1 in an n-dimensional space is non-trivial.
-/
lemma intersection_dim_pos {n : ℕ} (k : ℕ) (U V : Submodule ℝ (Fin n → ℝ))
  (hU : Module.finrank ℝ U = n - k)
  (hV : Module.finrank ℝ V = k + 1)
  (hk : k < n) :
  ∃ x ∈ U ⊓ V, x ≠ 0 := by
    by_contra h_contra;
    have h_dim_sum : Module.finrank ℝ (↥(U ⊔ V)) = Module.finrank ℝ U + Module.finrank ℝ V := by
      rw [ ← Submodule.finrank_sup_add_finrank_inf_eq, show U ⊓ V = ⊥ from eq_bot_iff.mpr fun x hx => Classical.not_not.mp fun hx' => h_contra ⟨ x, hx, hx' ⟩ ] ; aesop;
    linarith [ Nat.sub_add_cancel hk.le, show Module.finrank ℝ ( ↥ ( U ⊔ V ) ) ≤ n from le_trans ( Submodule.finrank_le _ ) ( by simp ) ]

/-
The dimension of the span of the first k+1 eigenvectors is k+1.
-/
lemma span_bot_dim {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (_ : A.IsSymm)
  (k : Fin n)
  (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
  Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : {j : Fin n // j ≤ k} => v i))) = k + 1 := by
    rw [ finrank_span_eq_card ];
    · rw [ Fintype.card_subtype ];
      rw [ show ( Finset.filter ( fun x => x ≤ k ) Finset.univ : Finset ( Fin n ) ) = Finset.Iic k by ext; simp +decide ] ; simp +decide;
    · have := v.orthonormal;
      exact this.linearIndependent.comp _ ( by aesop_cat )

/-
Definition of a principal submatrix.
-/
def principal_submatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Matrix S S ℝ :=
  A.submatrix Subtype.val Subtype.val

/-
Reindexed principal submatrix to Fin (card S).
-/
def principal_submatrix_fin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
  Matrix (Fin (Fintype.card {x // x ∈ S})) (Fin (Fintype.card {x // x ∈ S})) ℝ :=
  Matrix.reindex (Fintype.equivFin {x // x ∈ S}) (Fintype.equivFin {x // x ∈ S}) (principal_submatrix A S)

/-
The principal submatrix of a symmetric matrix is symmetric.
-/
lemma principal_submatrix_fin_isSymm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (S : Finset (Fin n)) :
  (principal_submatrix_fin A S).IsSymm := by
    unfold principal_submatrix_fin;
    unfold principal_submatrix; aesop;

/-
The dimension of the subspace of vectors supported on S is |S|.
-/
def subspace_of_support {n : ℕ} (S : Finset (Fin n)) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (Set.range (fun i : S => (Pi.single (i : Fin n) 1 : Fin n → ℝ)))

lemma subspace_of_support_dim {n : ℕ} (S : Finset (Fin n)) :
  Module.finrank ℝ (subspace_of_support S) = S.card := by
    -- The subspace_of_support S is isomorphic to the space of functions from S to ℝ, which has dimension |S|.
    have h_iso : subspace_of_support S ≃ₗ[ℝ] (S → ℝ) := by
      -- The subspace of vectors with support in S is isomorphic to the space of functions from S to ℝ.
      have h_iso : (↥(subspace_of_support S)) ≃ₗ[ℝ] (S → ℝ) := by
        have h_subspace : subspace_of_support S = Submodule.span ℝ (Set.range (fun i : S => fun j : Fin n => if j = i then 1 else 0)) := by
          ext x; simp [subspace_of_support];
          congr!;
          aesop
        rw [ h_subspace ];
        refine' ( LinearEquiv.ofFinrankEq .. );
        rw [ @finrank_span_eq_card ] <;> norm_num;
        refine' Fintype.linearIndependent_iff.2 _;
        intro g hg i; replace hg := congr_fun hg i; simp_all +decide [ Finset.sum_ite ] ;
        rw [ Finset.sum_eq_single i ] at hg <;> aesop;
      exact h_iso;
    have := h_iso.finrank_eq;
    aesop

/-
The Rayleigh quotient is bounded by the maximum eigenvalue.
-/
lemma rayleigh_le_max_eigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (x : Fin n → ℝ) (hx : x ≠ 0) (hn : n ≠ 0) :
  rayleigh_quotient A x ≤ (sorted_eigenvalues A hA).getLast (List.ne_nil_of_length_pos (by
  rw [ sorted_eigenvalues_length A hA ] ; positivity)) := by
    classical
    set ev := sorted_eigenvalues A hA
    obtain ⟨ v, hv ⟩ := exists_orthonormal_basis_sorted A hA;
    -- Expand x in the orthonormal basis of eigenvectors provided by `exists_orthonormal_basis_sorted`.
    obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, x = ∑ i, c i • v i := by
      have := v.sum_repr x;
      exact ⟨ _, this.symm ⟩;
    -- Substitute $x = \sum c_i v_i$ into the Rayleigh quotient.
    have h_rayleigh_subst : rayleigh_quotient A x = (∑ i, c i ^ 2 * ev.get ⟨i, by
      simp [ev, sorted_eigenvalues_length]⟩) / (∑ i, c i ^ 2) := by
      have h_rayleigh : dotProduct x (A.mulVec x) = ∑ i, c i^2 * (ev.get ⟨i, by
        simp [ev, sorted_eigenvalues_length]⟩) := by
        have h_rayleigh : dotProduct (∑ i, c i • v i) (∑ i, c i • (ev.get ⟨i, by
          simp [ev, sorted_eigenvalues_length]⟩) • v i) = ∑ i, c i ^ 2 * ev.get ⟨i, by
          simp [ev, sorted_eigenvalues_length]⟩ := by
          have h_inner : ∀ i j : Fin n, dotProduct (v i) (v j) = if i = j then 1 else 0 := by
            intro i j; have := v.orthonormal; simp_all +decide [ orthonormal_iff_ite ] ;
            convert this i j using 1;
            simp +decide [ dotProduct, inner ];
            ac_rfl
          generalize_proofs at *;
          simp +decide [ dotProduct, Finset.sum_mul _ _ _, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm, sq ];
          simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_comm ];
          simp_all +decide [ dotProduct ]
        generalize_proofs at *;
        convert h_rayleigh using 2;
        rw [ hc, Matrix.mulVec_sum ];
        exact Finset.sum_congr rfl fun i _ => by rw [ Matrix.mulVec_smul, hv ] ;
      generalize_proofs at *;
      have h_rayleigh : dotProduct x x = ∑ i, c i^2 := by
        have h_rayleigh : ∀ i j, dotProduct (v i) (v j) = if i = j then 1 else 0 := by
          intro i j; have := v.orthonormal; simp_all +decide [ orthonormal_iff_ite ] ;
          convert this i j using 1;
          exact Finset.sum_congr rfl fun _ _ => by simp +decide [ mul_comm ] ;
        have h_rayleigh : ∀ i j, dotProduct (c i • v i) (c j • v j) = c i * c j * (if i = j then 1 else 0) := by
          simp +decide [ ← h_rayleigh, mul_assoc ];
          simp +decide [ dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm ];
        have h_rayleigh : dotProduct (∑ i, c i • v i) (∑ i, c i • v i) = ∑ i, ∑ j, dotProduct (c i • v i) (c j • v j) := by
          simp +decide only [dotProduct];
          simp +decide only [← Finset.sum_comm, ← Finset.mul_sum _ _ _, ← Finset.sum_mul];
          exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.sum_apply ] ;
        simp_all +decide [ sq ];
      unfold rayleigh_quotient; aesop;
    generalize_proofs at *;
    -- Since $\lambda_i \le \lambda_{\max}$, we have $\sum c_i^2 \lambda_i \le \lambda_{\max} \sum c_i^2$.
    have h_sum_le_max : ∑ i, c i ^ 2 * ev.get ⟨i, by
      simp [ev, sorted_eigenvalues_length]⟩ ≤ (∑ i, c i ^ 2) * ev.getLast ‹_› := by
      rw [ Finset.sum_mul _ _ _ ];
      gcongr;
      -- Since the list is sorted in non-decreasing order, the last element is the maximum.
      have h_sorted : ∀ (i j : Fin ev.length), i ≤ j → ev.get i ≤ ev.get j := by
        have h_sorted' : List.Sorted (· ≤ ·) ev := by
          simpa [ev] using sorted_eigenvalues_sorted A hA
        exact fun i j hij => h_sorted'.rel_get_of_le hij
      convert h_sorted _ _ _;
      rotate_left;
      exact ⟨ ev.length - 1, Nat.sub_lt ((List.length_pos_iff).mpr ‹_›) zero_lt_one ⟩;
      · exact Nat.le_sub_one_of_lt ( by solve_by_elim );
      · grind
    generalize_proofs at *;
    rw [ h_rayleigh_subst, div_le_iff₀ ];
    · linarith;
    · contrapose! hx;
      exact hc.trans ( Finset.sum_eq_zero fun i _ => by rw [ show c i = 0 by exact sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Finset.single_le_sum ( fun i _ => sq_nonneg ( c i ) ) ( Finset.mem_univ i ) ) hx ) ( sq_nonneg ( c i ) ) ) ] ; norm_num )

/-
The largest eigenvalue of a principal submatrix of size m is at least the m-th smallest eigenvalue of the original matrix.
-/
lemma eigenvalue_interlacing_max {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (S : Finset (Fin n)) (hS : S.Nonempty) :
  let m := S.card
  let subA := principal_submatrix_fin A S
  let h_subA := principal_submatrix_fin_isSymm A hA S
  let evs_A := sorted_eigenvalues A hA
  let evs_sub := sorted_eigenvalues subA h_subA
  evs_sub.getLast (List.ne_nil_of_length_pos (by
  rw [ sorted_eigenvalues_length ] ; aesop)) ≥ evs_A.get ⟨m - 1, by
    rw [ sorted_eigenvalues_length ];
    exact lt_of_lt_of_le ( Nat.sub_lt ( Finset.card_pos.mpr hS ) zero_lt_one ) ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )⟩ := by
    classical
    -- Let $V$ be the subspace of vectors supported on $S$. Its dimension is $m$.
    set V := subspace_of_support S;
    -- By the Min-Max principle, the $(m-1)$-th eigenvalue of $A$ is $\le \sup_{x \in V, x \ne 0} R_A(x)$.
    have h_min_max : (sorted_eigenvalues A hA).get ⟨S.card - 1, by
        rw [ sorted_eigenvalues_length ];
        exact lt_of_lt_of_le ( Nat.sub_lt ( Finset.card_pos.mpr hS ) zero_lt_one ) ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )⟩ ≤
        ⨆ (x : {x : V // x.1 ≠ 0}), rayleigh_quotient A x.1 := by
      apply le_sup_rayleigh_of_dim_eq_succ A hA ⟨S.card - 1, by
        exact lt_of_lt_of_le ( Nat.sub_lt ( Finset.card_pos.mpr hS ) zero_lt_one ) ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )⟩ V
      rw [ Nat.sub_add_cancel ( Finset.card_pos.mpr hS ) ] ; exact subspace_of_support_dim S;
    -- For any $x \in V$, let $y$ be the corresponding vector in $\mathbb{R}^m$. Then $R_A(x) = R_{subA}(y)$.
    have h_rayleigh_eq : ∀ x ∈ V, x ≠ 0 → ∃ y : Fin (Fintype.card {x // x ∈ S}) → ℝ, y ≠ 0 ∧ rayleigh_quotient A x = rayleigh_quotient (principal_submatrix_fin A S) y := by
      intro x hx hx_ne_zero
      obtain ⟨y, hy⟩ : ∃ y : Fin (Fintype.card {x // x ∈ S}) → ℝ, x = fun i => if h : i ∈ S then y (Fintype.equivFin {x // x ∈ S} ⟨i, h⟩) else 0 := by
        have h_span : ∀ x ∈ V, ∃ y : {x // x ∈ S} → ℝ, x = fun i => if h : i ∈ S then y ⟨i, h⟩ else 0 := by
          intro x hx
          obtain ⟨y, hy⟩ : ∃ y : {x // x ∈ S} → ℝ, x = ∑ i : {x // x ∈ S}, y i • (Pi.single (i : Fin n) 1 : Fin n → ℝ) := by
            have h_span : x ∈ Submodule.span ℝ (Set.range (fun i : {x // x ∈ S} => (Pi.single (i : Fin n) 1 : Fin n → ℝ))) := by
              exact hx;
            rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_span;
            obtain ⟨ c, rfl ⟩ := h_span; use fun i => c i; simp +decide [ Finsupp.sum_fintype ] ;
          use y; ext i; simp [hy];
          split_ifs <;> simp_all +decide [ Pi.single_apply ];
          · rw [ Finset.sum_eq_single ⟨ i, by assumption ⟩ ] <;> aesop;
          · exact Finset.sum_eq_zero fun x hx => if_neg <| by aesop;
        obtain ⟨ y, rfl ⟩ := h_span x hx;
        exact ⟨ fun i => y ( Fintype.equivFin { x // x ∈ S } |>.symm i ), by ext i; aesop ⟩;
      refine' ⟨ y, _, _ ⟩;
      · contrapose! hx_ne_zero; aesop;
      · unfold rayleigh_quotient;
        unfold principal_submatrix_fin;
        unfold principal_submatrix; simp +decide [ hy, Matrix.mulVec, dotProduct ] ;
        congr! 1;
        · rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
          · refine' Finset.sum_bij ( fun i hi => Fintype.equivFin { x // x ∈ S } ⟨ i, hi ⟩ ) _ _ _ _ <;> simp +decide;
            · exact fun b => ⟨ _, Finset.mem_coe.mp ( Fintype.equivFin { x // x ∈ S } |>.symm b |>.2 ), by simp +decide ⟩;
            · intro a ha; simp +decide [ ha ] ;
              rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
              · rw [ ← Finset.sum_coe_sort ];
                refine' Or.inl ( Finset.sum_bij ( fun i hi => Fintype.equivFin { x // x ∈ S } ⟨ i, by aesop ⟩ ) _ _ _ _ ) <;> simp +decide;
                exact fun b => ⟨ _, Finset.mem_coe.mp ( Fintype.equivFin { x // x ∈ S } |>.symm b |>.2 ), by simp +decide ⟩;
              · aesop;
          · aesop;
        · rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
          · refine' Finset.sum_bij ( fun i hi => Fintype.equivFin { x // x ∈ S } ⟨ i, hi ⟩ ) _ _ _ _ <;> simp +decide;
            · exact fun b => ⟨ _, Finset.mem_coe.mp ( Fintype.equivFin { x // x ∈ S } |>.symm b |>.2 ), by simp +decide ⟩;
            · aesop;
          · aesop;
    -- By `rayleigh_le_max_eigenvalue`, $R_{subA}(y) \le \lambda_{\max}(subA)$.
    have h_rayleigh_le_max : ∀ y : Fin (Fintype.card {x // x ∈ S}) → ℝ, y ≠ 0 →
        rayleigh_quotient (principal_submatrix_fin A S) y ≤
          (sorted_eigenvalues (principal_submatrix_fin A S) (principal_submatrix_fin_isSymm A hA S)).getLast
            (List.ne_nil_of_length_pos (by
              rw [ sorted_eigenvalues_length ];
              exact Fintype.card_pos_iff.mpr ⟨ ⟨ hS.choose, hS.choose_spec ⟩ ⟩ )) := by
      intros y hy_nonzero
      apply rayleigh_le_max_eigenvalue (principal_submatrix_fin A S) (principal_submatrix_fin_isSymm A hA S) y hy_nonzero;
      exact ne_of_gt ( Fintype.card_pos_iff.mpr ⟨ ⟨ hS.choose, hS.choose_spec ⟩ ⟩ );
    refine le_trans h_min_max ?_;
    convert ciSup_le _;
    · simp +zetaDelta at *;
      exact ⟨ _, Submodule.subset_span ⟨ ⟨ hS.choose, hS.choose_spec ⟩, rfl ⟩, ne_of_apply_ne ( fun x => x hS.choose ) ( by simp +decide ) ⟩;
    · grind

/-
If a principal submatrix of the Huang matrix has size > 2^(n-1), its maximum eigenvalue is at least sqrt(n).
-/
lemma huang_submatrix_max_eigenvalue_ge_sqrt_n {n : ℕ} (hn : n ≠ 0)
  (S : Finset (Fin (2^n))) (hS : S.card > 2^(n-1)) :
  let subA := principal_submatrix_fin (huang_matrix_fin n) S
  let h_subA := principal_submatrix_fin_isSymm (huang_matrix_fin n) (huang_matrix_fin_isSymm n) S
  let evs_sub := sorted_eigenvalues subA h_subA
  evs_sub.getLast (List.ne_nil_of_length_pos (by
  rw [ sorted_eigenvalues_length ];
  exact Fintype.card_pos_iff.mpr ⟨ Classical.choose ( Finset.card_pos.mp ( pos_of_gt hS ) ), Classical.choose_spec ( Finset.card_pos.mp ( pos_of_gt hS ) ) ⟩)) ≥ Real.sqrt n := by
    have h_max_eigenvalue_ge_sqrt : let m := S.card
      let subA := principal_submatrix_fin (huang_matrix_fin n) S
      let h_subA := principal_submatrix_fin_isSymm (huang_matrix_fin n) (huang_matrix_fin_isSymm n) S
      let evs_sub := sorted_eigenvalues subA h_subA
      evs_sub.getLast (List.ne_nil_of_length_pos (by
      have hSpos : 0 < S.card := lt_of_le_of_lt (Nat.zero_le _) hS
      have hlen : evs_sub.length = S.card := by
        simp [evs_sub, sorted_eigenvalues_length, Fintype.card_coe]
      rw [hlen]
      exact hSpos)) ≥ (sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)).get ⟨m - 1, by
        rw [ sorted_eigenvalues_length ];
        exact lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt hS ) ) ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )⟩ := by
        apply eigenvalue_interlacing_max;
        exact Finset.card_pos.mp ( pos_of_gt hS )
    have h_eigenvalues_eq_list : let evs := sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)
      evs = List.replicate (2^(n-1)) (-Real.sqrt n) ++ List.replicate (2^(n-1)) (Real.sqrt n) := by
        exact huang_eigenvalues_eq_list n hn
    simp_all +decide [ List.getElem_append ];
    exact le_trans ( by rw [ if_neg ( by omega ) ] ) h_max_eigenvalue_ge_sqrt

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
Checking SimpleGraph.induce
-/
/-
Definition of the induced subgraph of the hypercube graph on S.
-/
def induced_hypercube_graph {n : ℕ} (S : Finset (Fin n → Bool)) : SimpleGraph {x // x ∈ S} :=
  SimpleGraph.induce (S : Set (Fin n → Bool)) (hypercube_graph n)

/-
Definition of the hypercube graph on Fin (2^n).
-/
def hypercube_graph_fin (n : ℕ) : SimpleGraph (Fin (2^n)) :=
  (hypercube_graph n).map (boolFunEquivFin n).toEmbedding

/-
Definition of the induced subgraph of the hypercube graph on S, mapped to Fin (card S).
-/
def induced_hypercube_graph_fin_card {n : ℕ} (S : Finset (Fin (2^n))) : SimpleGraph (Fin (Fintype.card {x // x ∈ S})) :=
  let G := SimpleGraph.induce (S : Set (Fin (2^n))) (hypercube_graph_fin n)
  let equiv := Fintype.equivFin {x // x ∈ S}
  G.map equiv.toEmbedding

/-
The absolute values of the reindexed Huang matrix entries correspond to the adjacency of the reindexed hypercube graph.
-/
lemma abs_huang_fin_eq_adjacency_fin {n : ℕ} (i j : Fin (2^n)) :
  |huang_matrix_fin n i j| = if (hypercube_graph_fin n).Adj i j then 1 else 0 := by
    -- Apply the result that |huang_matrix u v| = 1 if u~v else 0.
    have h_abs : ∀ u v : Fin n → Bool, |(huang_matrix n) u v| = if (hypercube_graph n).Adj u v then 1 else 0 := by
      -- By definition of $A_n$, we know that $|A_n u v| = 1$ if $u$ and $v$ are adjacent in the hypercube graph, and $|A_n u v| = 0$ otherwise.
      intros u v
      simp [abs_huang_eq_adjacency, hypercube_graph];
      by_cases h : u = v <;> simp +decide [ h, eq_comm ];
    unfold huang_matrix_fin;
    unfold hypercube_graph_fin; aesop;

/-
The entries of the principal submatrix of the Huang matrix are bounded by the adjacency matrix of the induced subgraph.
-/
lemma huang_submatrix_bounded_by_induced_adjacency {n : ℕ} (S : Finset (Fin (2^n))) (i j : Fin (Fintype.card {x // x ∈ S})) :
  |principal_submatrix_fin (huang_matrix_fin n) S i j| ≤ if (induced_hypercube_graph_fin_card S).Adj i j then 1 else 0 := by
    unfold principal_submatrix_fin induced_hypercube_graph_fin_card;
    simp +decide [ principal_submatrix ];
    split_ifs <;> simp_all +decide [ abs_huang_fin_eq_adjacency_fin ];
    · split_ifs <;> norm_num;
    · rename_i h;
      contrapose! h;
      use (Fintype.equivFin { x // x ∈ S }).symm i, by
        exact Finset.mem_coe.mp ( Subtype.mem _ ), (Fintype.equivFin { x // x ∈ S }).symm j, by
        exact ( Fintype.equivFin { x // x ∈ S } ).symm j |>.2
      generalize_proofs at *;
      aesop

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

/-
A boolean function of degree n has sensitivity at least sqrt(n).
-/
theorem sensitivity_ge_sqrt_degree_of_degree_eq_n {n : ℕ} (f : (Fin n → Bool) → Bool) (h_deg : degree f = n) (hn : n ≠ 0) :
  (sensitivity f : ℝ) ≥ Real.sqrt n := by
  classical
  -- Reduce to any level set with the "right" adjacency-count equality.
  have h_main :
      ∀ (S0 : Finset (Fin n → Bool)),
        (∀ x ∈ S0,
            (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S0) Finset.univ).card =
              (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y) Finset.univ).card) →
        S0.card > 2^(n-1) →
        (sensitivity f : ℝ) ≥ Real.sqrt n := by
    intro S0 h_eq hS0
    -- Reindex S0 to Fin (2^n).
    let S : Finset (Fin (2^n)) := S0.map (boolFunEquivFin n).toEmbedding
    have hS : S.card > 2^(n-1) := by
      simp [S, hS0]
    let subA := principal_submatrix_fin (huang_matrix_fin n) S
    let h_subA := principal_submatrix_fin_isSymm (huang_matrix_fin n) (huang_matrix_fin_isSymm n) S
    let evs_sub := sorted_eigenvalues subA h_subA

    -- Nonempty list witness for the spectral bounds.
    have hnS : Fintype.card {x // x ∈ S} ≠ 0 := by
      have hSpos : 0 < S.card := lt_of_le_of_lt (Nat.zero_le _) hS
      rw [Fintype.card_coe]
      exact ne_of_gt hSpos
    have h_ne : evs_sub ≠ [] := by
      apply List.ne_nil_of_length_pos
      dsimp [evs_sub]
      rw [sorted_eigenvalues_length]
      exact Nat.pos_of_ne_zero hnS

    -- Lower bound on λ_max from interlacing.
    have hpos_sub : 0 < Fintype.card {x // x ∈ S} := by
      exact Fintype.card_pos_iff.mpr
        ⟨ ⟨ Classical.choose (Finset.card_pos.mp (pos_of_gt hS)),
            Classical.choose_spec (Finset.card_pos.mp (pos_of_gt hS)) ⟩ ⟩
    have h_ne0 : evs_sub ≠ [] := by
      apply List.ne_nil_of_length_pos
      dsimp [evs_sub]
      rw [sorted_eigenvalues_length]
      exact hpos_sub
    have h_lower0 :
        Real.sqrt n ≤ evs_sub.getLast h_ne0 := by
      simpa [subA, h_subA, evs_sub, h_ne0] using
        (huang_submatrix_max_eigenvalue_ge_sqrt_n (n := n) hn S hS)
    have h_lower : Real.sqrt n ≤ evs_sub.getLast h_ne := by
      have h_eq_last :
          evs_sub.getLast h_ne0 = evs_sub.getLast h_ne := by
        exact
          (List.getLast_congr (l₁ := evs_sub) (l₂ := evs_sub)
            (h₁ := h_ne0) (h₂ := h_ne) (h₃ := rfl))
      rw [← h_eq_last]
      exact h_lower0

    -- Upper bound on λ_max by max degree of the induced graph.
    have h_adj :
        ∀ i j,
          |subA i j| ≤ if (induced_hypercube_graph_fin_card S).Adj i j then 1 else 0 := by
      intro i j
      simpa [subA] using (huang_submatrix_bounded_by_induced_adjacency (S := S) i j)
    have h_lambda_le_max :
        evs_sub.getLast h_ne ≤ (induced_hypercube_graph_fin_card S).maxDegree := by
      simpa [subA, h_subA, evs_sub, h_ne] using
        (spectral_radius_bound (A := subA) (hA := h_subA)
          (G := induced_hypercube_graph_fin_card S) h_adj hnS)

    -- Max degree of the induced graph is at most sensitivity.
    let G0 : SimpleGraph {x // x ∈ (S0 : Set (Fin n → Bool))} :=
      (hypercube_graph n).induce (S0 : Set (Fin n → Bool))
    let G1 : SimpleGraph {x // x ∈ (S : Set (Fin (2^n)))} :=
      (hypercube_graph_fin n).induce (S : Set (Fin (2^n)))
    -- Prefer the `Subtype.fintype` instance to avoid instance mismatch in neighbor finsets.
    letI : Fintype {x // x ∈ (S0 : Set (Fin n → Bool))} := by
      classical
      exact (Subtype.fintype (p := fun x => x ∈ (S0 : Set (Fin n → Bool))))
    let eS : {x // x ∈ (S0 : Set (Fin n → Bool))} ≃ {x // x ∈ (S : Set (Fin (2^n)))} :=
      { toFun := fun x =>
          ⟨ (boolFunEquivFin n) x.1,
            by
              have hx0 : x.1 ∈ S0 := by
                exact Finset.mem_coe.mp x.2
              show (boolFunEquivFin n) x.1 ∈ S
              exact Finset.mem_map.mpr ⟨ x.1, hx0, rfl ⟩ ⟩
        invFun := fun y =>
          ⟨ (boolFunEquivFin n).symm y.1,
            by
              have hy : y.1 ∈ S := by
                exact Finset.mem_coe.mp y.2
              rcases Finset.mem_map.mp hy with ⟨ x0, hx0, hx0eq ⟩
              have hx0eq' : (boolFunEquivFin n).symm y.1 = x0 := by
                have h := congrArg (fun z => (boolFunEquivFin n).symm z) hx0eq
                simp at h
                exact h.symm
              have hx0' : (boolFunEquivFin n).symm y.1 ∈ S0 := by
                rw [hx0eq']
                exact hx0
              exact hx0' ⟩
        left_inv := by
          intro x; ext; simp
        right_inv := by
          intro y; ext; simp }
    let iso1 : G0 ≃g G1 :=
      { toEquiv := eS
        map_rel_iff' := by
          intro a b
          -- Reduce to adjacency in the base graphs, then use the map-adj lemma.
          change (hypercube_graph_fin n).Adj (eS a).1 (eS b).1 ↔ (hypercube_graph n).Adj a.1 b.1
          simp [hypercube_graph_fin, eS] }
    let equivS := Fintype.equivFin {x // x ∈ S}
    have iso2 : G1 ≃g induced_hypercube_graph_fin_card S := by
      dsimp [induced_hypercube_graph_fin_card, G1]
      exact SimpleGraph.Iso.map equivS G1
    let iso : G0 ≃g induced_hypercube_graph_fin_card S := iso2.comp iso1

    have h_deg_le_G0 : ∀ v0 : {x // x ∈ S0}, G0.degree v0 ≤ sensitivity f := by
      intro v0
      have h_map := SimpleGraph.map_neighborFinset_induce
        (G := hypercube_graph n) (s := (S0 : Set (Fin n → Bool))) v0
      have h_card :
          (G0.neighborFinset v0).card =
            ((hypercube_graph n).neighborFinset v0 ∩ S0).card := by
        have h_card' := congrArg Finset.card h_map
        simpa [G0, Finset.card_map, Finset.toFinset_coe, -SimpleGraph.card_neighborFinset_eq_degree] using
          h_card'
      have h_filter :
          (hypercube_graph n).neighborFinset v0 ∩ S0 =
            Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ y ∈ S0) Finset.univ := by
        ext y
        simp [SimpleGraph.neighborFinset_eq_filter, Finset.mem_inter, Finset.mem_filter]
      have h_degree_formula :
          G0.degree v0 =
            (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ y ∈ S0) Finset.univ).card := by
        have h_card'' :
            (G0.neighborFinset v0).card =
              (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ y ∈ S0) Finset.univ).card := by
          rw [← h_filter]
          exact h_card
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact h_card''
      have h_eq' := h_eq v0.1 (by exact Finset.mem_coe.mp v0.2)
      have h_card_le :
          (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ f v0 ≠ f y) Finset.univ).card
            ≤ sensitivity f := by
        unfold sensitivity
        have :=
          Finset.le_sup (s := Finset.univ)
            (f := fun x =>
              Finset.card
                (Finset.filter
                  (fun y =>
                    (Finset.card
                        (Finset.filter (fun i => x i ≠ y i) Finset.univ) = 1) ∧ f x ≠ f y)
                  Finset.univ))
            (by simp : (v0 : Fin n → Bool) ∈ (Finset.univ : Finset (Fin n → Bool)))
        simp [hypercube_graph_adj]
        exact this
      calc
        G0.degree v0
            = (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ y ∈ S0) Finset.univ).card := h_degree_formula
        _ = (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ f v0 ≠ f y) Finset.univ).card := h_eq'
        _ ≤ sensitivity f := h_card_le

    have h_maxDegree_le : (induced_hypercube_graph_fin_card S).maxDegree ≤ sensitivity f := by
      refine SimpleGraph.maxDegree_le_of_forall_degree_le (G := induced_hypercube_graph_fin_card S)
        (k := sensitivity f) ?_
      intro i
      let v0 := iso.symm i
      have hdeg : (induced_hypercube_graph_fin_card S).degree i = G0.degree v0 := by
        classical
        have hcard := Fintype.card_congr (iso.mapNeighborSet v0)
        have hiso :
            (induced_hypercube_graph_fin_card S).degree (iso v0) = G0.degree v0 := by
          calc
            (induced_hypercube_graph_fin_card S).degree (iso v0) =
                Fintype.card ((induced_hypercube_graph_fin_card S).neighborSet (iso v0)) := by
                  symm
                  simpa using
                    (SimpleGraph.card_neighborSet_eq_degree
                      (G := induced_hypercube_graph_fin_card S) (v := iso v0))
            _ = Fintype.card (G0.neighborSet v0) := by
                  simpa using hcard.symm
            _ = G0.degree v0 := by
                  simpa using (SimpleGraph.card_neighborSet_eq_degree (G := G0) (v := v0))
        have hv0 : iso v0 = i := by
          -- `iso` is an equivalence; rewrite with `Equiv.apply_symm_apply`.
          simp [v0]
        have hiso' := hiso
        rw [hv0] at hiso'
        exact hiso'
      rw [hdeg]
      exact h_deg_le_G0 v0

    -- Combine the bounds.
    have h_maxDegree_le' : (induced_hypercube_graph_fin_card S).maxDegree ≤ (sensitivity f : ℕ) := h_maxDegree_le
    have h_upper : evs_sub.getLast h_ne ≤ (sensitivity f : ℝ) := by
      exact le_trans h_lambda_le_max (by exact_mod_cast h_maxDegree_le')

    exact le_trans h_lower h_upper

  -- Pick the large level set (S_pos or S_neg).
  have h_large := exists_large_level_set f h_deg hn
  cases h_large with
  | inl hpos =>
      apply h_main (S_pos f)
      · intro x hx
        simpa using (sensitivity_at_x_eq_degree_in_S_pos f x hx).symm
      · exact hpos
  | inr hneg =>
      apply h_main (S_neg f)
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
