import Lean
import LeanLemmanaid.Template
import LeanLemmanaid.TypedAbstraction
import LeanLemmanaid.Elaboration

open Lean Meta Elab Command Term
open TypedAbstraction

-- def instantiateTemplate (expr : tempExpr) (subst : Array Expr) : TermElabM Expr := do
--   let (_, s) ← (exprInfer expr).run {}
--   let thm ← withFullContext s fun ctx => do
--     let e₀ ← elabTempExpr expr ctx.termMap
--     let e₁ ← instantiateMVars e₀
--     -- logInfo s!"{e₁}"
--     let e₂ ← Lean.Meta.mkForallFVars (ctx.vars.map (fun p => p.2)) e₁
--     let params := ctx.typeParams ++ (ctx.consts.map (fun p => p.2)) ++ (ctx.ops.map (fun p => p.2))
--     let template := e₂.abstract params
--     if subst.size != params.size then
--       throwError m!"Arity mismatch! Template has {params.size} variables, but input has {subst.size} arguments."
--     let result := template.instantiateRev subst
--     try
--       check result
--       Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
--       let finalResult ← instantiateMVars result
--       let abstractResult ← Lean.Meta.abstractMVars finalResult
--       let finalTheorem := abstractResult.expr
--       let thm ← Lean.Meta.lambdaTelescope finalTheorem fun fvars body => do
--         Lean.Meta.mkForallFVars fvars body
--       pure thm
--     catch ex =>
--       throwError "instantiateTemplate failed: {ex.toMessageData}"
--   return thm


def termIsHole (stx : Term) : Bool := stx.raw.isOfKind ``Lean.Parser.Term.hole

def holeBI : tempLit → BinderInfo
  | .typeHole .. | .sort .. => .implicit
  | _ => .default

/-- Elaborate a *provided* (non-`_`) argument for a parameter hole against its
expected type `ty`. Operators additionally fall back to elaborating with no
expected type — their recorded type is instance-stripped, so e.g. `ite`
(`[Decidable c]`) fails defeq against it and must keep the instance binder for the
application site. The fallback is opHole-only: a `.const` like `0 : Fin _` failing
should error, not silently re-elaborate as `Nat`. -/
def fillArg : tempLit → Term → Expr → TermElabM Expr
  | .opHole .., stx, ty => do
      let st ← saveState
      try elabTerm stx (some ty)
      catch _ => st.restore; elabTerm stx none
  | _, stx, ty => elabTerm stx (some ty)

def instantiateCore (t : Template) (substStx : Array Term) (sortedCtx : List (tempLit × tempExpr)) : TempElabM Expr := do
  -- `bound` accumulates, in dependency order, every fvar that becomes a binder of
  -- the resulting theorem: value vars, sorts, and parameter holes left as `_`.
  let rec go (ctx : List (tempLit × tempExpr)) (argIdx : Nat) (bound : Array Expr) :
      TempElabM (Expr × Nat) := do
    match ctx with
    | [] =>
        let body ← elabTempExpr' t.statement
        -- Resolve deferred typeclass mvars (registered by applyExplicitArgs) BEFORE
        -- checking: at this point the whole statement is built and every operator's
        -- type parameters have been pinned, so instance goals are concrete.
        synthesizeSyntheticMVarsNoPostponing
        let body ← instantiateMVars body
        check body
        let result ← mkForallFVars bound body
        return (result, argIdx)
    | (hole, typeExpr) :: rest =>
        let ty ← elabTempExpr' typeExpr
        match hole with
        | .var .. =>
            withLocalDecl (hole.mkName) BinderInfo.default ty fun fvar => do
              modify (fun env => env.insert (.lit hole) fvar)
              go rest argIdx (bound.push fvar)
        | .sort .. =>
            withLocalDecl (hole.mkName) BinderInfo.implicit ty fun fvar => do
              modify (fun env => env.insert (.lit hole) fvar)
              go rest argIdx (bound.push fvar)
        | .typeHole .. | .const .. | .opHole .. =>
            if h : argIdx < substStx.size then
              if termIsHole substStx[argIdx] then
                -- `_`: keep the parameter abstract — bind it as an fvar (a peer of
                -- vars/sorts), so it never becomes a capturing metavariable.
                withLocalDecl (hole.mkName) (holeBI hole) ty fun fvar => do
                  modify (fun env => env.insert (.lit hole) fvar)
                  go rest (argIdx + 1) (bound.push fvar)
              else
                let arg ← fillArg hole substStx[argIdx] ty
                modify (fun env => env.insert (.lit hole) arg)
                go rest (argIdx + 1) bound
            else
              throwError m!"Missing arguments! Template expects more than {substStx.size} arguments."
  let (result, argCount) ← go sortedCtx 0 #[]
  if argCount != substStx.size then
    throwError m!"Arity mismatch! Template has {argCount} variables, but input has {substStx.size} arguments."
  return result

/-- Blind-swap instantiation (experimental).

Build the *fully abstract* fvar skeleton via `withContext` (every hole becomes an
fvar of its template type), elaborate the statement against it, then:
  * keep the value-vars and sorts as binders (`mkForallFVars`), and
  * blindly `replaceFVars` the parameter holes (types / consts / ops) with the
    pre-elaborated `subst` terms.

No expected-type guidance, no per-occurrence operator application — this is the
"old" style, kept deliberately naive so we can see exactly what it can and can't
handle on the test suite. -/
def instantiateCore' (t : Template) (subst : Array Expr) : TermElabM Expr := do
  match topologicalSort t.ctx with
  | .error err =>
      throwError m!"Check for circular type dependency: {err}"
  | .ok sortedCtx =>
    let action : TempElabM Expr := do
      withContext sortedCtx do
        -- Body built against the skeleton: every hole resolves to its fvar.
        let body ← elabTempExpr' t.statement
        let s ← get
        -- Partition the skeleton fvars: value-vars / sorts stay quantified,
        -- parameters get swapped for the supplied terms (in sortedCtx order,
        -- which is the order the user provided `subst`).
        let mut binderFVars := #[]
        let mut paramFVars := #[]
        for (hole, _) in sortedCtx do
          let some fvar := s.get? (.lit hole)
            | throwError m!"{repr hole} not found in skeleton!"
          match hole with
          | .var .. | .sort .. => binderFVars := binderFVars.push fvar
          | .typeHole .. | .const .. | .opHole .. => paramFVars := paramFVars.push fvar
        unless subst.size == paramFVars.size do
          throwError m!"Arity mismatch! Template has {paramFVars.size} parameters, \
                        but input has {subst.size} arguments."
        let quantified ← mkForallFVars binderFVars body
        return quantified.replaceFVars paramFVars subst
    let e ← action.run {}
    return e.1

/-- Wrapper around `instantiateCore'` mirroring `instantiateTemplate`'s epilogue
(check / synth / abstract leftover mvars / re-quantify). -/
def instantiateTemplate' (t : Template) (subst : Array Expr) : TermElabM Expr := do
  try
    let result ← instantiateCore' t subst
    check result
    synthesizeSyntheticMVarsNoPostponing
    let finalResult ← instantiateMVars result
    let abstractResult ← Lean.Meta.abstractMVars finalResult
    let thm := abstractResult.expr
    let finalThm ← Lean.Meta.lambdaTelescope thm fun fvars body => do
      Lean.Meta.mkForallFVars fvars body
    return finalThm
  catch ex =>
    throwError "instantiateTemplate' (blind swap) failed: {ex.toMessageData}"


def instantiateTemplate (t : Template) (substStx : Array Term) : TermElabM Expr := do
  match topologicalSort t.ctx with
  | .error err => throwError m!"Check for circular type dependency: {err}"
  | .ok sortedCtx =>
    try
      let result ← (instantiateCore t substStx sortedCtx).run' {}
      check result
      synthesizeSyntheticMVarsNoPostponing
      let finalResult ← instantiateMVars result
      let abstractResult ← Lean.Meta.abstractMVars finalResult
      let thm := abstractResult.expr
      let finalThm ← Lean.Meta.lambdaTelescope thm fun fvars body => do
        Lean.Meta.mkForallFVars fvars body
      return finalThm
    catch ex =>
      throwError "instantiateTemplate failed: {ex.toMessageData}"
