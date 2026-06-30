import Lean
import LeanLemmanaid.Template
import LeanLemmanaid.TypedAbstraction
import LeanLemmanaid.Elaboration
import LeanLemmanaid.TempEnvironment
import LeanLemmanaid.Instantiation

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
      -- `TermElabM` actions can be lifted into `TempElabM`, but not vice versa. Need to run
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


elab tk:"#instantiate" name:ident "with" "#[" args:term,* "]" : command =>
  liftTermElabM do
    -- let _ ← resolveGlobalConstNoOverload name
    let env ← getEnv
    match (templateExt.getState env).find? name.getId with
    | none =>
        withRef name <| throwError "Unknown template `{name}`"
    | some t =>
        let thm ← instantiateTemplate t (args.getElems)
        -- let subst ← args.getElems.mapM (fun a => elabTerm a none)
        -- let thm ← instantiateTemplate' t  subst
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
