import Lean
import LeanLemmanaid.Template
import LeanLemmanaid.TypedAbstraction

open Lean Meta Elab Command Term
open TypedAbstraction

/-!
# Elaboration

## Defintions
- elabTempExpr' : Elaborate a `tempExpr` into a `Lean.Expr`. For logical operators, just match the patterns and, for the literals (vars, opHoles, consts, types), obtain them from context.
- withContext : Build the lean context from the sorted `template.ctx` and run the continuation `k`. Makes nested localDecls.
-/

/-- Fill the leading non-explicit binders of `f`'s type, stopping at the next
explicit binder (or when the type is no longer a pi).

Implicit / strict-implicit binders become fresh metavariables. Instance-implicit
binders become *registered* synthetic typeclass metavariables: we do NOT
synthesize them eagerly here. Eager synthesis would fail for leading instances
(e.g. `@HAdd.hAdd`'s `[HAdd α β γ]`), whose type parameters are still
unassigned at this point. Instead we register each instance position as a
`.typeClass` synthetic mvar and let the `synthesizeSyntheticMVarsNoPostponing`
pass (run later, once the whole application is built) resolve them — by which
time both type-parameter-dependent (`HAdd`) and value-parameter-dependent
(`ite`'s `[Decidable c]`) instances have concrete goals. -/
partial def fillNonExplicitBinders (f : Expr) : TermElabM Expr := do
  match (← whnf (← inferType f)) with
  | .forallE _ domain _ .instImplicit =>
      let inst ← mkFreshExprMVar (some (← instantiateMVars domain)) (kind := .synthetic)
      registerSyntheticMVarWithCurrRef inst.mvarId! (.typeClass none)
      fillNonExplicitBinders (f.app inst)
  | .forallE _ _ _ .implicit | .forallE _ _ _ .strictImplicit =>
      let mvar ← mkFreshExprMVar none
      fillNonExplicitBinders (f.app mvar)
  | _ => return f

/-- Apply `fn` to its `explicitArgs`, inserting the non-explicit binders that sit
before/between explicit positions via `fillNonExplicitBinders`.

Each explicit argument is unified against its expected domain before being
applied. This is what pins the operator's implicit type parameters (e.g.
`HAdd`'s `α β`), so that the deferred instance goals registered by
`fillNonExplicitBinders` become concrete by the time typeclass synthesis runs.
A bare `Expr.app` would not perform this unification. -/
def applyExplicitArgs (fn : Expr) (explicitArgs : Array Expr) : TermElabM Expr := do
  let mut f := fn
  for arg in explicitArgs do
    f ← fillNonExplicitBinders f
    match (← whnf (← inferType f)) with
    | .forallE _ domain _ _ =>
        let argType ← inferType arg
        unless (← isDefEq argType domain) do
          throwError m!"Operator argument type mismatch: expected {domain}, got {argType}"
    | _ => pure ()
    f := f.app arg
  -- resolve any trailing non-explicit binders after the last explicit arg
  fillNonExplicitBinders f

abbrev TempElabM := StateRefT (Std.HashMap tempExpr Expr) TermElabM

partial def elabTempExpr' : tempExpr → TempElabM Expr
  | .lit (.sort (some idx)) =>
    return Expr.sort (Level.ofNat idx)
  | .lit (.sort none) =>
    return Expr.sort (← mkFreshLevelMVar)
  | .lit l@(.var _) | .lit l@(.const _) => do
    let ctx ← get
    match ctx.get? (.lit l) with
    | some fvar => return fvar
    | none => throwError m!"{repr l} not found!"

  | .lit (.opHole idx args) => do
    let ctx ← get
    let fnFvar ← match ctx.get? (.lit (.opHole idx #[])) with
      | some fvar => pure fvar
      | none => throwError m!"H{idx} not found!"
    let elabArgs ← args.mapM (fun arg => elabTempExpr' (.lit arg))
    applyExplicitArgs fnFvar elabArgs

  | .lit (.typeHole idx args) => do
    let ctx ← get
    let fnFvar ← match ctx.get? (.lit (.typeHole idx #[])) with
      | some fvar => pure fvar
      | none => throwError m!"T{idx} not found!"
    let elabArgs ← args.mapM (fun arg => elabTempExpr' (.lit arg))
    return mkAppN fnFvar elabArgs

  | .eq l r => do
    let lExpr ← elabTempExpr' (.lit l)
    let rExpr ← elabTempExpr' (.lit r)
    mkEq lExpr rExpr
  | .un _ e =>
    return mkApp (mkConst ``Not) (← elabTempExpr' e)
  | .bin op l r => do
    let lExpr ← elabTempExpr' l
    let rExpr ← elabTempExpr' r
    match op with
    | .and => return mkAnd lExpr rExpr
    | .or => return mkOr lExpr rExpr
    | .iff => return mkIff lExpr rExpr
    | .imp => return Expr.forallE `_ lExpr rExpr .default
  | .bind op idx varTy body => do
      let tyExpr ← elabTempExpr' varTy
      withLocalDecl (mkVarName idx) .default tyExpr fun fvar => do
        modify (·.insert (.lit (.var idx)) fvar)     -- so body's `.var idx` resolves here
        let bodyExpr ← elabTempExpr' body
        match op with
        | .forall => mkForallFVars #[fvar] bodyExpr
        | .exists => mkAppM ``Exists #[← mkLambdaFVars #[fvar] bodyExpr]


partial def withContext {α : Type} (sortedCtx : List (tempLit × tempExpr))
  (k : TempElabM α) : TempElabM α := do
  match sortedCtx with
  | [] => k
  | (hole, typeExpr) :: rest =>
    let ty ← elabTempExpr' typeExpr
    let bi := match hole with
    | .typeHole .. | .sort .. => BinderInfo.implicit
    | _ => BinderInfo.default
    withLocalDecl (hole.mkName) bi ty fun newFVar => do
      modify (fun env => env.insert (.lit hole) newFVar)
      withContext rest k

def Template.getFVars (t : Template) : TempElabM (Array Expr) := do
  let s ← get
  let mut fvars := #[]
  for (v, _) in t.ctx do
    match v with
    | .var .. => do
        let fvar := s.get? (.lit v)
        match fvar with
        | none => throwError m!"{repr v} not found!"
        | some fvar => fvars := fvars.push fvar
    | _ => continue
  return fvars

def Template.getParams (t : Template) : TempElabM (Array Expr) := do
  let s ← get
  let mut params := #[]
  for (v, _) in t.ctx do
    match v with
    | .typeHole .. | .opHole .. | .const .. =>
        let some fvar := s.get? (.lit v)
          | throwError m!"Fatal: Parameter {repr v} not found in state!"
        params := params.push fvar
    | _ => continue
  return params
