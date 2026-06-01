import Lean
import LeanLemmanaid.Template
set_option trace.debug true

open Lean Meta Elab Command Term

/- Dictionary for -/
structure templateState where
  typedVars : Std.HashMap Nat Expr := {}
  typedConsts : Std.HashMap Nat Expr := {}
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

def getConstType (idx : Nat) : TemplateM Expr := do
  let state ← get
  match state.typedConsts.get? idx with
  | some c => return c
  | none =>
    let x ← mkFreshExprMVar (← mkFreshTypeMVar)
    modify fun s => {s with typedConsts := s.typedConsts.insert idx x}
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

partial def termInfer : tempLit → TemplateM Expr
  | .var idx =>
    getVarType idx
  | .const idx =>
    getConstType idx
  | .opHole idx args => do
    let state ← get
    let argTypes ← args.mapM termInfer
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

partial def setToProp (e : Expr) : TemplateM Unit := do
  let e ← instantiateMVars e
  match e with
  | .forallE _ _ body _ =>
      setToProp body
  | _ =>
      unless ← isDefEq e (.sort .zero) do
        throwError "Expected Prop"

partial def exprInfer : tempExpr → TemplateM Expr
  | .lit l => do
      let t ← termInfer l
      setToProp t
      return mkSort levelZero
  | .eq l r => do
      let tl ← termInfer l
      let tr ← termInfer r
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

def collectTypeMVars (s : templateState) : MetaM (List MVarId) := do
  let mut out : List MVarId := []

  for (_, ty) in s.typedVars.toList do
    let ty ← instantiateMVars ty
    out := out ++ (← getMVars ty).toList

  for (_, ty) in s.typedConsts.toList do
    let ty ← instantiateMVars ty
    out := out ++ (← getMVars ty).toList

  for (_, ty) in s.typedOps.toList do
    let ty ← instantiateMVars ty
    out := out ++ (← getMVars ty).toList

  return out.eraseDups

structure TemplateContext where
  termMap : Std.HashMap Name Expr := {}
  typeParams : Array Expr := #[]
  vars : Array (Nat × Expr) := #[]
  consts : Array (Nat × Expr) := #[]
  ops : Array (Nat × Expr) := #[]

-- Functions to sort by first component
def insertSortedByIdx (x : Nat × Expr) : List (Nat × Expr) → List (Nat × Expr)
  | [] => [x]
  | y :: ys =>
      if x.1 ≤ y.1 then
        x :: y :: ys
      else
        y :: insertSortedByIdx x ys

def sortByIdx (xs : List (Nat × Expr)) : List (Nat × Expr) :=
  xs.foldr insertSortedByIdx []

-- A helper to declare the term variables (x's, c's and H's) once types are ready
partial def withTermVars {α : Type} (vars : List (Nat × Expr)) (const : List (Nat × Expr))
    (ops : List (Nat × Expr))
    (typeMap : Std.HashMap MVarId Expr)
    (typeParams : Array Expr)
    (k : TemplateContext → MetaM α) : MetaM α := do
  let rec go
      (vList : List (Nat × Expr))
      (cList : List (Nat × Expr))
      (oList : List (Nat × Expr))
      (ctx : TemplateContext) : MetaM α := do
    match vList, cList, oList with
    -- While there is an untyped variable
    | (idx, rawType) :: vRest, _, _=>
        let name := mkVarName idx -- Name it
        let abstractType ← instantiateMVars rawType -- Assume it has some type

        let concreteType := abstractType.replace fun e =>
          match e with | .mvar mvarId => typeMap.get? mvarId | _ => none

        withLocalDecl name BinderInfo.default concreteType fun fvar => do
          go vRest cList oList
            { ctx with
              termMap := ctx.termMap.insert name fvar
              vars := ctx.vars.push (idx, fvar) }

    | [], (idx, rawType) :: cRest, _ =>
        let name := mkConstName idx
        let abstractType ← instantiateMVars rawType

        let concreteType := abstractType.replace fun e =>
          match e with
          | .mvar mvarId => typeMap.get? mvarId
          | _ => none
        withLocalDecl name BinderInfo.default concreteType fun fvar => do
          go [] cRest oList
            { ctx with
              termMap := ctx.termMap.insert name fvar
              consts := ctx.consts.push (idx, fvar) }

    | [], [], (idx, rawType) :: oRest =>
        let name := mkOpName idx
        let abstractType ← instantiateMVars rawType

        let concreteType := abstractType.replace fun e =>
          match e with | .mvar mvarId => typeMap.get? mvarId | _ => none

        withLocalDecl name BinderInfo.default concreteType fun fvar => do
          go [] [] oRest
            { ctx with
              termMap := ctx.termMap.insert name fvar
              ops := ctx.ops.push (idx, fvar) }

    | [], [], [] => k ctx
  go (sortByIdx vars) (sortByIdx const) (sortByIdx ops) { typeParams := typeParams }

partial def withTypeVars {α : Type} (mvars : List MVarId)
    (k : Std.HashMap MVarId Expr → Array Expr → MetaM α): MetaM α := do
  let rec go (xs : List MVarId)
    (ctx : Std.HashMap MVarId Expr)
    (typeParams : Array Expr) := do
    match xs with
    | [] =>
        k ctx typeParams
    | mv :: rest =>
      withLocalDecl (mkTypeName (typeParams.size + 1))
        BinderInfo.implicit (mkSort levelOne)
        fun fvar => do
          go rest (ctx.insert mv fvar) (typeParams.push fvar)
  go mvars {} #[]

def withFullContext {α : Type} (s : templateState)
    (k : TemplateContext → MetaM α) : MetaM α := do
    -- This k business is continuation (used to chain function calls, so that they all happen sequentially... Basically leaving room for the actual elaboration, because this only builds context)
  let mvars ← collectTypeMVars s
  withTypeVars mvars fun typeMap typeParams => do
    withTermVars s.typedVars.toList s.typedConsts.toList s.typedOps.toList typeMap typeParams fun ctx => do
      k ctx

partial def elabTempTerm (lit : tempLit) (varMap : Std.HashMap Name Expr) : MetaM Expr := do
  match lit with
  | .var k =>
      return varMap.get! (mkVarName k)

  | .const k =>
      return varMap.get! (mkConstName k)

  | .opHole n args =>
      let fvar := varMap.get! (mkOpName n)
      let mut argExprs := #[]
      for arg in args do
        argExprs := argExprs.push (← elabTempTerm arg varMap)
      return mkAppN fvar argExprs

partial def elabTempExpr (expr : tempExpr) (varMap : Std.HashMap Name Expr) : MetaM Expr := do
  match expr with
  | .lit l => do
      elabTempTerm l varMap

  | .eq l r => do
      let lExpr ← elabTempTerm l varMap
      let rExpr ← elabTempTerm r varMap
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
      | .iff =>
          return mkApp2 (mkConst ``Iff) lExpr rExpr
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
  withFullContext s fun ctx => do
    elabTempExpr e ctx.termMap

elab tk:"#test_stx" t:template : command => runTermElabM fun _ => do
  let e ← elabTemp t
  let (_, s) ← (exprInfer e).run {}
  withRef tk <| discard <|
    withFullContext s fun ctx => do
      let leanExpr ← elabTempExpr e ctx.termMap
      let dummyGoal ← mkFreshExprMVar leanExpr
      let holeInfo :=
        s!"holes vars={repr (ctx.vars.map (fun p => p.1))}, consts={repr (ctx.consts.map (fun p => p.1))}, ops={repr (ctx.ops.map (fun p => p.1))}"
      logInfo m!"{holeInfo}"
      logInfo (MessageData.ofGoal dummyGoal.mvarId!)

      return leanExpr

-- #test_stx H1 x1 x2
-- #test_stx H1 x1 x2 = H1 x2 x1

-- #test_stx H1 c1 x1 = x1
-- #test_stx H1 x1 c1 = x1

-- #test_stx H1 (H2 x1 x2) (H3 x1 x2) = H1 (H3 x2 x1) (H2 x1 x2)
-- #test_stx ∀ x1, ∃ x2, H1 x1 → H2 x2
-- #test_stx H1 x1 x2 = x1 ∨ H1 x1 x2 = x2

-- #test_stx ∀ x1 x2, H1 x1 x2 = c1 ∨ H1 x1 x2 = c2
