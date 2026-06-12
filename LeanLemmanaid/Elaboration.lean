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

abbrev TempElabM := StateRefT (Std.HashMap tempExpr Expr) MetaM

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
    return mkAppN fnFvar elabArgs

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
  | .bind op idx body => do
      let fvar ← elabTempExpr' (.lit (.var idx))
      let bodyExpr ← elabTempExpr' body
      match op with
      | .forall => mkForallFVars #[fvar] bodyExpr
      | .exists =>
          let lambdaBody ← mkLambdaFVars #[fvar] bodyExpr
          mkAppM ``Exists #[lambdaBody]

partial def withContext {α : Type} (sortedCtx : List (tempLit × tempExpr))
  (k : TempElabM α) : TempElabM α := do
  match sortedCtx with
  | [] => k
  | (hole, typeExpr) :: rest =>
    let ty ← elabTempExpr' typeExpr
    withLocalDecl (hole.mkName) BinderInfo.default ty fun newFVar => do
      modify (fun env => env.insert (.lit hole) newFVar)
      withContext rest k

elab tk:"#abstract " id:ident : command => runTermElabM fun _ => do
  -- 1. Resolve the theorem from Mathlib/Lean
  let name ← resolveGlobalConstNoOverload id
  let info ← getConstInfo name
  let type ← instantiateMVars info.type
  let (t, _) ← (abstractTypedTemplate type).run {}
  match topologicalSort t.ctx with
  | .error err => logError m!"Topological sort failed: {err}"
  | .ok sortedCtx =>
      let action : TempElabM Unit := do
        withContext sortedCtx do
          let leanExpr ← elabTempExpr' t.statement
          let dummyGoal ← mkFreshExprMVar leanExpr
          withRef tk <| logInfo (MessageData.ofGoal dummyGoal.mvarId!)
          return ()
      let _ ← action.run {}

-- #abstract Fin.exists_iff
