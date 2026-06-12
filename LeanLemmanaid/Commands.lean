import Lean
import LeanLemmanaid.Template
-- import LeanLemmanaid.Unifier

open Lean Meta Elab Command Term

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


-- elab tk:"#inst_temp" t:template "with" "#[" args:term,* "]" : command =>
--   liftTermElabM do
--     let expr ← elabTemp t
--     -- logInfo s!"{expr}"
--     let subst ← args.getElems.mapM (elabTerm · none)
--     let thm ← instantiateTemplate expr subst
--     withRef tk <| logInfo m!"{thm}"
