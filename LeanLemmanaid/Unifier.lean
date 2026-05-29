import Lean
import LeanLemmanaid.Template
set_option trace.debug true

open Lean Meta Elab Command Term

/- Dictionary for -/
structure templateState where
  typedVars : Std.HashMap Nat Expr := {}
  typedOps : Std.HashMap Nat Expr := {}

#check StateRefT'
abbrev TemplateM := StateRefT templateState MetaM

def getVarType (idx : Nat) : TemplateM Expr := do
  let state ← get
  match state.typedVars.get? idx with
  | some x => return x
  | none =>
    let x ← mkFreshExprMVar (← mkFreshTypeMVar)
    modify fun s => { s with typedVars := s.typedVars.insert idx x}
    return x

/- This function is only for lookup and placeholder creation -/
def getOpType (idx : Nat) : TemplateM Expr := do
  let state ← get
  match state.typedOps.get? idx with
  | some f => return f
  | none =>
    let f ← mkFreshExprMVar (← mkFreshTypeMVar)
    modify fun s => { s with typedOps := s.typedOps.insert idx f}
    return f

partial def termInfer : tempLit → TemplateM Unit
  | .var idx =>
      discard <| getVarType idx     -- Do the work and return nothing
  | .opHole idx args => do
      discard <| getOpType idx
      args.forM termInfer           -- Apply monadic action to each element of Array

partial def termInfer' : tempLit → TemplateM Expr
  | .var idx =>
    getVarType idx
  | .opHole idx args => do
    let state ← get
    let argTypes ← args.mapM termInfer'
    match state.typedOps.get? idx with
    | some T =>
      let outType ← mkFreshTypeMVar
      let expectedType ← argTypes.foldrM (fun a b => mkArrow a b) outType

      unless ← isDefEq T expectedType do
        throwError "Operator application type mismatch"
      return outType

    | none =>
      let outType ← mkFreshTypeMVar
      let opType ← argTypes.foldrM (fun a b => mkArrow a b) outType
      modify fun s => { s with typedOps := s.typedOps.insert idx opType }
      return outType

partial def naiveInfer : tempExpr → TemplateM Unit
  | .lit l => do
    termInfer l
  | .eq l r => do
    termInfer l
    termInfer r
  | .un _ e => do
    naiveInfer e
  | .bin _ el er => do
    naiveInfer el
    naiveInfer er
  | .bind _ idx e => do
    discard <| getVarType idx
    naiveInfer e

partial def setToProp (e : Expr) : TemplateM Unit := do
  let e ← instantiateMVars e
  match e with
  | .forallE _ _ body _ =>
      setToProp body
  | _ =>
      unless ← isDefEq e (.sort .zero) do
        throwError "Expected Prop"

partial def notSoNaiveInfer : tempExpr → TemplateM Unit
  | .lit l => do
      discard <| termInfer' l
  | .eq l r => do
      let tl ← termInfer' l
      let tr ← termInfer' r
      unless ← isDefEq tl tr do
        throwError "Equality type mismatch"
  | .un _ e => do
    notSoNaiveInfer e
  | .bin _ el er => do
    notSoNaiveInfer el
    notSoNaiveInfer er
  | .bind _ idx e => do
    discard <| getVarType idx
    notSoNaiveInfer e

partial def exprInfer : tempExpr → TemplateM Expr
  | .lit l => do
      let t ← termInfer' l
      setToProp t
      return mkSort levelZero
  | .eq l r => do
      let tl ← termInfer' l
      let tr ← termInfer' r
      unless ← isDefEq tl tr do
        throwError "Equality type mismatch"
      return mkSort levelZero
  | .un _ e => do
    let t ← exprInfer e
    setToProp t
    return mkSort levelZero
  | .bin _ el er => do
    let tl ← exprInfer el
    setToProp tl
    let tr ← exprInfer er
    setToProp tr
    return mkSort levelZero
  | .bind _ idx e => do
    discard <| getVarType idx
    let t ← exprInfer e
    setToProp t
    return mkSort levelZero

elab tk:"#test_inference" b:("!")? t:template : command => runTermElabM fun _ => do
  let e ← elabTemp t
  if b.isSome then
    let (_, s) ← (exprInfer e).run {}
    let mut out := ""
    for (k,v) in s.typedVars.toList do
      let ty ← instantiateMVars v
      out := out ++ s!"x{k} : {ty}\n"
    for (k,v) in s.typedOps.toList do
      let ty ← instantiateMVars v
      out := out ++ s!"H{k} : {ty}\n"
     withRef tk (logInfo m!"{out}")
  else
    let (_, s) ← (naiveInfer e).run {}
    let mut out := ""
    for (k,v) in s.typedVars.toList do
      let ty ← instantiateMVars v
      out := out ++ s!"x{k} : {ty}\n"
    for (k,v) in s.typedOps.toList do
      let ty ← instantiateMVars v
      out := out ++ s!"H{k} : {ty}\n"

    withRef tk (logInfo m!"{out}")

#test_inference H1 x1 x2 = H1 x2 x1
#test_inference H1 x1 x2 = H2 x1 x2
#test_inference H1 (H2 x1 x2) (H3 x1 x2) = H1 (H3 x2 x1) (H2 x1 x2)
#test_inference ∀ x1, ∃ x2, H1 x1 → H2 x2

#test_inference! H1 x1 x2
#test_inference! H1 x1 x2 = H1 x2 x1
#test_inference! H1 (H2 x1 x2) (H3 x1 x2) = H1 (H3 x2 x1) (H2 x1 x2)
#test_inference! ∀ x1, ∃ x2, H1 x1 → H2 x2
#test_inference! H1 x1 x2 = x1 ∨ H1 x1 x2 = x2

partial def withTypeVars {α : Type} (mvars : List MVarId)
    (k : Std.HashMap MVarId Expr → MetaM α): MetaM α := do
  let rec go (xs : List MVarId)
    (ctx : Std.HashMap MVarId Expr) := do
    match xs with
    | [] =>
        k ctx
    | mv :: rest =>
      withLocalDecl (mkTypeName (ctx.size + 1))
        BinderInfo.default (mkSort levelOne)
        fun fvar => do
          go rest (ctx.insert mv fvar)
  go mvars {}

def collectTypeMVars (s : templateState) : MetaM (List MVarId) := do
  let mut out : List MVarId := []

  for (_, ty) in s.typedVars.toList do
    let ty ← instantiateMVars ty
    out := out ++ (← getMVars ty).toList

  for (_, ty) in s.typedOps.toList do
    let ty ← instantiateMVars ty
    out := out ++ (← getMVars ty).toList

  return out.eraseDups

-- elab "#test_ctx" t:template : command => runTermElabM fun _ => do
--   let e ← elabTemp t
--   let (_, s) ← (exprInfer e).run {}
--   let mvars ← collectTypeMVars s

--   discard <|
--     withTypeVars mvars fun _ => do
--       let dummyGoal ← mkFreshExprMVar (mkConst ``True)
--       let goalStr ← Lean.Meta.ppGoal dummyGoal.mvarId!
--       logInfo goalStr

--       return mkConst ``True

-- A helper to declare the term variables (x's and H's) once types are ready
def withTermVars {α : Type} (vars : List (Nat × Expr)) (ops : List (Nat × Expr))
    (typeMap : Std.HashMap MVarId Expr)
    (k : Std.HashMap Name Expr → MetaM α) : MetaM α := do
  let rec go
      (vList : List (Nat × Expr))
      (oList : List (Nat × Expr))
      (ctx : Std.HashMap Name Expr) : MetaM α := do
    match vList, oList with
    | (idx, rawType) :: vRest, _ =>
        let name := mkVarName idx
        let abstractType ← instantiateMVars rawType

        let concreteType := abstractType.replace fun e =>
          match e with | .mvar mvarId => typeMap.get? mvarId | _ => none

        withLocalDecl name BinderInfo.default concreteType fun fvar => do
          go vRest oList (ctx.insert name fvar)

    | [], (idx, rawType) :: oRest =>
        let name := mkOpName idx
        let abstractType ← instantiateMVars rawType

        let concreteType := abstractType.replace fun e =>
          match e with | .mvar mvarId => typeMap.get? mvarId | _ => none

        withLocalDecl name BinderInfo.default concreteType fun fvar => do
          go [] oRest (ctx.insert name fvar)

    | [], [] => k ctx

  go vars ops {}

def withFullContext {α : Type} (s : templateState)
    (k : Std.HashMap Name Expr → MetaM α) : MetaM α := do
  let mvars ← collectTypeMVars s
  withTypeVars mvars fun typeMap => do
    withTermVars s.typedVars.toList s.typedOps.toList typeMap fun varMap => do
      k varMap

partial def elabTerm (lit : tempLit) (varMap : Std.HashMap Name Expr) : MetaM Expr := do
  match lit with
  | .var k =>
      return varMap.get! (mkVarName k)

  | .opHole n args =>
      let fvar := varMap.get! (mkOpName n)
      let mut argExprs := #[]
      for arg in args do
        argExprs := argExprs.push (← elabTerm arg varMap)
      return mkAppN fvar argExprs

partial def elabTempExpr (expr : tempExpr) (varMap : Std.HashMap Name Expr) : MetaM Expr := do
  match expr with
  | .lit l => do
      elabTerm l varMap

  | .eq l r => do
      let lExpr ← elabTerm l varMap
      let rExpr ← elabTerm r varMap
      mkEq lExpr rExpr
  | .un _ e => do
      let eExpr ← elabTempExpr e varMap
      return mkApp (mkConst ``Not) eExpr
  | .bin op l r =>
      let lExpr ← elabTempExpr l varMap
      let rExpr ← elabTempExpr r varMap

      match op with
      | .and =>
          return mkApp2 (mkConst ``And) lExpr rExpr
      | .or =>
          return mkApp2 (mkConst ``Or) lExpr rExpr
      | .imp =>
          return Expr.forallE `_ lExpr rExpr .default
  | .bind op idx body =>
      let fvar := varMap.get! (mkVarName idx)
      let bodyExpr ← elabTempExpr body varMap

      match op with
      | .forall =>
          mkForallFVars #[fvar] bodyExpr

      | .exists =>
          let lambdaBody ← mkLambdaFVars #[fvar] bodyExpr
          mkAppM ``Exists #[lambdaBody]

def elabTemplate (t : TSyntax `template) : MetaM Expr := do
  let e ← elabTemp t
  let (_, s) ← (exprInfer e).run {}
  withFullContext s fun varMap => do
    elabTempExpr e varMap

elab tk:"#test_stx" t:template : command => runTermElabM fun _ => do
  let e ← elabTemp t
  let (_, s) ← (exprInfer e).run {}
  withRef tk <| discard <|
    withFullContext s fun varMap => do
      let leanExpr ← elabTempExpr e varMap
      let dummyGoal ← mkFreshExprMVar leanExpr
      logInfo (MessageData.ofGoal dummyGoal.mvarId!)

      return leanExpr

elab tk:"#test_stx " t:template : command => runTermElabM fun _ => do
  let e ← elabTemp t
  let (_, s) ← (exprInfer e).run {}
  withRef tk <| discard <|
    withFullContext s fun varMap => do
      let leanExpr ← elabTempExpr e varMap
      let dummyGoal ← mkFreshExprMVar leanExpr
      logInfo (MessageData.ofGoal dummyGoal.mvarId!)
      return leanExpr

#test_stx H1 x1 x2
#test_stx H1 x1 x2 = H1 x2 x1
#test_stx H1 (H2 x1 x2) (H3 x1 x2) = H1 (H3 x2 x1) (H2 x1 x2)
#test_stx ∀ x1, ∃ x2, H1 x1 → H2 x2
#test_stx H1 x1 x2 = x1 ∨ H1 x1 x2 = x2

#test_stx ∀ x1 x2, H1 x1 x2 = x1 ∨ H1 x1 x2 = x2
