import Lean
import LeanLemmanaid.Template
import LeanLemmanaid.TypedAbstraction
import LeanLemmanaid.Elaboration
import LeanLemmanaid.TempEnvironment

open Lean Meta Elab Command Term
open TypedAbstraction

elab tk:"#test_delab " t:template_stx : command =>
  liftTermElabM do
    let e ← elabTemp t
    let t' ← delabExpr e
    withRef tk <| logInfo m!"original: {t}\ndelabbed: {t'}"

elab tk:"#test_typed_abs " id:ident : command => runTermElabM fun _ => do
  let name ← resolveGlobalConstNoOverload id
  let info ← getConstInfo name
  let type ← instantiateMVars info.type
  let (t, _) ← (abstractTypedTemplate type).run {}
  let stx ← delabExpr t.statement
  withRef tk <| logInfo m!"\n{t.ctx}\n{stx}"

def showTemplate (t : Template) : TermElabM Unit := do
  match topologicalSort t.ctx with
  | .error err =>
      throwError m!"Check for circular type dependency: {err}"

  | .ok sortedCtx =>
      let action : TempElabM Unit := do
        withContext sortedCtx do
          let prop ← elabTempExpr' t.statement
          let dummyGoal ← mkFreshExprMVar prop
          logInfo (MessageData.ofGoal dummyGoal.mvarId!)
      let _ ← action.run {}

def abstractTheorem (name : Name) : MetaM Template := do
  let info ← getConstInfo name
  let type ← instantiateMVars info.type
  let (t, _) ← (abstractTypedTemplate type).run {}
  return t

elab "abstract " id:ident : term => fun _ => do
  let name ← resolveGlobalConstNoOverload id
  let t ← abstractTheorem name
  return toExpr t

elab tk:"#abstract " id:ident : command =>
  liftTermElabM do
  let name ← resolveGlobalConstNoOverload id
  let t ← abstractTheorem name
  withRef tk <| showTemplate t

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

def instantiateCore (t : Template) (substStx : Array Term) (sortedCtx : List (tempLit × tempExpr)) : TempElabM Expr := do
  let rec go (ctx : List (tempLit × tempExpr)) (argIdx : Nat) : TempElabM (Expr × Nat) := do
    match ctx with
    | [] =>
        let body ← elabTempExpr' t.statement
        -- Resolve deferred typeclass mvars (registered by applyExplicitArgs) BEFORE
        -- checking: at this point the whole statement is built and every operator's
        -- type parameters have been pinned, so instance goals are concrete.
        synthesizeSyntheticMVarsNoPostponing
        let body ← instantiateMVars body
        check body
        let s ← get
        let mut fvars := #[]
        for (v, _) in sortedCtx do
          match v with
          | .var .. =>
              let some fvar := s.get? (.lit v)
                | throwError m!"{repr v} not found!"
              fvars := fvars.push fvar
          | _ => continue
        let result ← mkForallFVars fvars body
        return (result, argIdx)
    | (hole, typeExpr) :: rest =>
        let ty ← elabTempExpr' typeExpr
        match hole with
        | .var .. =>
            withLocalDecl (hole.mkName) BinderInfo.default ty fun fvar => do
              modify (fun env => env.insert (.lit hole) fvar)
              go rest argIdx
        | .typeHole .. | .const .. =>
            if h : argIdx < substStx.size then
              let arg ← elabTerm substStx[argIdx] (some ty)
              modify (fun env => env.insert (.lit hole) arg)
              go rest (argIdx + 1)
            else
              throwError m!"Arity mismatch! Template expects more than {substStx.size} arguments."
        | .opHole .. =>
            if h : argIdx < substStx.size then
              -- Prefer elaborating the operator against its recorded (instance-
              -- stripped) type. This pins implicit type parameters that are fixed by
              -- the RESULT type rather than by an explicit argument (e.g. `Int.cast`'s
              -- `R`, which leaves `IntCast ?R` stuck otherwise) and gives `_`
              -- placeholders a concrete function type so they can be applied.
              --
              -- But for operators whose genuine type contains an instance binder the
              -- recorded type lacks (e.g. `ite`'s `[Decidable c]`, which sits after an
              -- explicit arg and was stripped during abstraction), this elaboration
              -- fails defeq. In that case fall back to elaborating with no expected
              -- type, letting the instance binder survive to the application site
              -- where `applyExplicitArgs` registers it as a typeclass mvar to be
              -- synthesized once its argument is concrete.
              let arg ← show TermElabM Expr from do
                let st ← saveState
                try
                  elabTerm substStx[argIdx] (some ty)
                catch _ =>
                  st.restore
                  elabTerm substStx[argIdx] none
              modify (fun env => env.insert (.lit hole) arg)
              go rest (argIdx + 1)
            else
              throwError m!"Arity mismatch! Template expects more than {substStx.size} arguments."
        | .sort .. =>
            withLocalDecl (hole.mkName) BinderInfo.implicit ty fun fvar => do
              modify (fun env => env.insert (.lit hole) fvar)
              go rest argIdx
  let (result, argCount) ← go sortedCtx 0
  if argCount != substStx.size then
    throwError m!"Arity mismatch! Template has {argCount} variables, but input has {substStx.size} arguments."
  return result

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

elab tk:"#instantiate" name:ident "with" "#[" args:term,* "]" : command =>
  liftTermElabM do
    -- let _ ← resolveGlobalConstNoOverload name
    let env ← getEnv
    match (templateExt.getState env).find? name.getId with
    | none =>
        withRef name <| throwError "Unknown template `{name}`"
    | some t =>
        let thm ← instantiateTemplate t (args.getElems)
        withRef tk <| logInfo m!"{thm}"

elab "template " name:ident " := " thm:ident : command => do
  let t ← liftTermElabM do
    abstractTheorem (← resolveGlobalConstNoOverload thm)
  modifyEnv fun env =>
    templateExt.addEntry env (name.getId, t)
  -- let decl ← `(def $name : Template := abstract $thm)
  -- elabCommand decl

elab "template " name:ident " := " stx:template_stx " where " ctx:template_ctx,* : command => do
  let t ← liftTermElabM do
    let stmt ← elabTemp stx
    let ctxEntries ← ctx.getElems.toList.mapM (fun c => liftMetaM (elabTempCtx c))
    match TypedAbstraction.topologicalSort ctxEntries with
    | Except.error msg => throwError msg
    | Except.ok sortedCtx => return { ctx := sortedCtx, statement := stmt }
  modifyEnv fun env =>
    templateExt.addEntry env (name.getId, t)

elab tk:"#show_template" name:ident : command =>
  liftTermElabM do
  -- let _ ← resolveGlobalConstNoOverload name
  let env ← getEnv
  match (templateExt.getState env).find? name.getId with
  | some t => withRef tk <| showTemplate t
  | none => withRef name <| throwError "Unknown template `{name}`"
