import Lean
import LeanLemmanaid.Template

open Lean Meta Elab Command Term

/-!
# Typed Abstraction

This module contains the abstraction pipeline to obtain the template of a theorem.
A `template` contains the context, a list of term-type tuples along with the statement.

## Main Definitions

- abstractProp : Abstraction for the statement of the template, builds a `tempExpr` from the `Expr` of the theorem
- abstractTerm : Term-level abstraction, builds a `tempLit` from an `Expr`
- abstractType : Type-level abstraction, builds a `tempExpr` from an `Expr`, intended to bue used for the types of terms in the statement
- abstractContext : Abstraction for the context of the template, builds `template.ctx` a list of term-type tuples for all the terms that appear in the statement, along with their types.
- abstractTypedTemplate : Top-level abstraction. Builds a `template` from an `Expr` of the theorem using the above functions. Also sorts the context by dependency. Also removes leading binders (i.e. parameters) from the statement and puts them in the context.
-/

namespace TypedAbstraction

structure AbstractionState where
  simpleTypes : Std.HashMap Expr Nat := {}
  vars : Std.HashMap FVarId (Nat × Expr) := {}
  consts : Std.HashMap Expr (Nat × Expr) := {}
  ops : Std.HashMap Expr (Nat × Expr) := {}

abbrev AbstractionState.isEmpty (s : AbstractionState) := s.simpleTypes.isEmpty && s.vars.isEmpty &&
       s.consts.isEmpty && s.ops.isEmpty

abbrev AbstractM := StateRefT AbstractionState MetaM

def getTypeCount : AbstractM Nat := do
  return (← get).simpleTypes.keys.length + 1

def getVarCount : AbstractM Nat := do
  return (← get).vars.keys.length + 1

def getConstCount : AbstractM Nat := do
  return (← get).consts.keys.length + 1

def getOpCount : AbstractM Nat := do
  return (← get).ops.keys.length + 1

def getTypeIdx (typeExpr : Expr) : AbstractM Nat := do
  let typeExpr := typeExpr.consumeMData
  let s ← get
  match s.simpleTypes.get? typeExpr with
  | some idx => return idx
  | none =>
      let idx ← getTypeCount
      modify fun s => { s with simpleTypes := s.simpleTypes.insert typeExpr idx }
      return idx

def getVarIdx (fvarId : FVarId) : AbstractM (Nat × Expr) := do
  let s ← get
  match s.vars.get? fvarId with
  | some pair => return pair
  | none =>
      let idx ← getVarCount
      let ty ← inferType (.fvar fvarId)
      modify fun s => { s with vars := s.vars.insert fvarId (idx, ty) }
      return (idx, ty)

def getVarIdxWithType (fvarId : FVarId) (ty : Expr) : AbstractM (Nat × Expr) := do
  let s ← get
  match s.vars.get? fvarId with
  | some pair => return pair
  | none =>
      let idx ← getVarCount
      modify fun s => { s with vars := s.vars.insert fvarId (idx, ty) }
      return (idx, ty)

def getOpIdx (head : Expr) : AbstractM (Nat × Expr) := do
  let head := head.consumeMData
  let s ← get
  match s.ops.get? head with
  | some pair => return pair
  | none =>
      let idx ← getOpCount
      let ty ← inferType head
      modify fun s => { s with ops := s.ops.insert head (idx, ty) }
      return (idx, ty)

def getConstIdx (c : Expr) : AbstractM (Nat × Expr) := do
  let c := c.consumeMData
  let s ← get
  match s.consts.get? c with
  | some pair => return pair
  | none =>
      let idx ← getConstCount
      let ty ← inferType c
      modify fun s => { s with consts := s.consts.insert c (idx, ty) }
      return (idx, ty)

/- Returns two arrays: non-explicit arguments applied to the head, and explicit
arguments that should appear as template arguments. -/
partial def sortAppArgs (fn : Expr) (args : Array Expr) : MetaM (Array Expr × Array Expr) := do
  let mut fnType ← inferType fn
  let mut implMasked := #[]
  let mut expl := #[]
  for arg in args do
    let t ← whnf fnType
    match t with
    | .forallE _ _ body bi =>
        if bi == BinderInfo.default then
          expl := expl.push arg
        else
          implMasked := implMasked.push arg
        fnType := body.instantiate1 arg
    | _ =>
        throwError m!"Cannot read application arity for {fn}; expected a function type, got {t}"
  return (implMasked, expl)

partial def sortAppArgsWithTypes (fn : Expr) (args : Array Expr) :
    MetaM (Array Expr × Array (Expr × Expr)) := do
  let mut fnType ← inferType fn
  let mut implMasked := #[]
  let mut expl := #[]
  for arg in args do
    let t ← whnf fnType
    match t with
    | .forallE _ domain body bi =>
        if bi == BinderInfo.default then
          expl := expl.push (arg, domain)
        else
          implMasked := implMasked.push arg
        fnType := body.instantiate1 arg
    | _ =>
        throwError m!"Cannot read application arity for {fn}; expected a function type, got {t}"
  return (implMasked, expl)

/- Returns an array of all explicit arguments of a function application. -/
partial def explicitAppArgs (fn : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  let mut fnType ← inferType fn
  let mut out := #[]
  for arg in args do
    let t ← whnf fnType
    match t with
    | .forallE _ _ body bi =>
        if bi == BinderInfo.default then
          out := out.push arg
        fnType := body.instantiate1 arg
    | _ =>
        throwError m!"Cannot read application arity for {fn}; expected a function type, got {t}"
  return out

def withAbstractedVar {α : Type} (name : Name) (bi : BinderInfo) (type : Expr)
    (k : Nat → Expr → AbstractM α) : AbstractM α := do
  withLocalDecl name bi type fun fvar => do
    let (idx, _) ← getVarIdx fvar.fvarId!
    k idx fvar

def withIgnoredLocal {α : Type} (name : Name) (bi : BinderInfo) (type : Expr)
    (k : Expr → AbstractM α) : AbstractM α := do
  withLocalDecl name bi type k

def isPropSafe (e : Expr) : MetaM Bool := do
  try
    isProp e
  catch _ =>
    return false

mutual
  partial def abstractProp (e : Expr) : AbstractM tempExpr := do
    let e := e.consumeMData
    match e with
    | .app .. =>
        let fn := e.getAppFn.consumeMData
        let args := e.getAppArgs
        match fn with
        | .const ``Eq _ =>
            let explArgs ← liftM <| explicitAppArgs fn args
            unless explArgs.size == 2 do
              throwError m!"Expected equality to have 2 explicit arguments, got {explArgs.size}: {e}"
            return .eq (← abstractTerm explArgs[0]!) (← abstractTerm explArgs[1]!)
        | .const ``Not _ =>
            let explArgs ← liftM <| explicitAppArgs fn args
            unless explArgs.size == 1 do
              throwError m!"Expected negation to have 1 explicit argument, got {explArgs.size}: {e}"
            return .un .not (← abstractProp explArgs[0]!)
        | .const ``And _ =>
            let explArgs ← liftM <| explicitAppArgs fn args
            unless explArgs.size == 2 do
              throwError m!"Expected conjunction to have 2 explicit arguments, got {explArgs.size}: {e}"
            return .bin .and (← abstractProp explArgs[0]!) (← abstractProp explArgs[1]!)
        | .const ``Or _ =>
            let explArgs ← liftM <| explicitAppArgs fn args
            unless explArgs.size == 2 do
              throwError m!"Expected disjunction to have 2 explicit arguments, got {explArgs.size}: {e}"
            return .bin .or (← abstractProp explArgs[0]!) (← abstractProp explArgs[1]!)
        | .const ``Iff _ =>
            let explArgs ← liftM <| explicitAppArgs fn args
            unless explArgs.size == 2 do
              throwError m!"Expected iff to have 2 explicit arguments, got {explArgs.size}: {e}"
            return .bin .iff (← abstractProp explArgs[0]!) (← abstractProp explArgs[1]!)
        | .const ``Exists _ =>
            let explArgs ← liftM <| explicitAppArgs fn args
            unless explArgs.size == 1 do
              throwError m!"Expected existential to have 1 explicit predicate argument, got {explArgs.size}: {e}"
            match explArgs[0]!.consumeMData with
            | .lam name type body bi =>
                withAbstractedVar name bi type fun idx fvar => do
                  return .bind .exists idx (← abstractProp (body.instantiate1 fvar))
            | pred =>
                throwError m!"Expected existential predicate to be a lambda, got {pred}"
        | _ =>
            return .lit (← abstractTerm e)
    | .forallE name type body bi =>
        if ← liftM <| isProp type then
          return .bin .imp (← abstractProp type) (← abstractProp body)
        else if bi == BinderInfo.default then
          withAbstractedVar name bi type fun idx fvar => do
            return .bind .forall idx (← abstractProp (body.instantiate1 fvar))
        else
          withIgnoredLocal name bi type fun fvar => do
            abstractProp (body.instantiate1 fvar)
    | .fvar _ =>
        if ← liftM <| isProp e then
          return .lit (.opHole (← getOpIdx e).1 #[])
        else
          throwError m!"Expected proposition, got term variable {e}"
    | .mvar .. | .bvar .. | .lam .. | .letE .. =>
        throwError m!"Unsupported in proposition abstraction: {e}"
    | .mdata _ e' => abstractProp e'
    | .lit .. | .const .. | .sort .. | .proj .. =>
        if ← liftM <| isProp e then
          return .lit (.opHole (← getOpIdx e).1 #[])
        else
          throwError m!"Expected proposition, got {e}"

  partial def abstractTerm (e : Expr) : AbstractM tempLit := do
    let e := e.consumeMData

    if !(e.hasFVar || e.hasMVar || e.hasLooseBVars) then
      if !(← liftM <| isProp e) then
        let ty ← liftM <| whnf (← inferType e)
        if !ty.isForall && !ty.isSort then
          return .const (← getConstIdx e).1

    match e with
    | .fvar fvarId =>
        let s ← get
        if let some pair := s.vars.get? fvarId then
          return .var pair.1
        if ← liftM <| isPropSafe e then
          return .opHole (← getOpIdx e).1 #[]
        else
          return .var (← getVarIdx fvarId).1
    | .app .. =>
        let fn := e.getAppFn.consumeMData
        let args := e.getAppArgs
        match fn with
        | .const ``Eq _ | .const ``Not _ | .const ``And _ | .const ``Or _ | .const ``Exists _ =>
            throwError m!"Logical proposition used as a term: {e}"
        | _ =>
            let (implArgs, explArgs) ← liftM <| sortAppArgs fn args
            let partialAppFn := mkAppN fn implArgs
            let argLits ← explArgs.mapM abstractTerm
            return .opHole (← getOpIdx partialAppFn).1 argLits
    | .const .. =>
        if ← liftM <| isProp e then
          return .opHole (← getOpIdx e).1 #[]
        let ty ← liftM <| whnf (← inferType e)
        if ty.isForall then
          return .opHole (← getOpIdx e).1 #[]
        if ty.isSort then
          return .opHole (← getOpIdx e).1 #[]
        return .const (← getConstIdx e).1
    | .lit .. =>
        return .const (← getConstIdx e).1
    | .mdata _ e' =>
        abstractTerm e'
    | .mvar .. | .bvar .. | .lam .. | .forallE ..
    | .letE .. | .sort .. | .proj .. =>
        throwError m!"Unsupported in term abstraction: {e}"

  partial def abstractTypeLit (e : Expr) : AbstractM tempLit := do
    let e := e.consumeMData
    if ← liftM <| isPropSafe e then
      return .opHole (← getOpIdx e).1 #[]
    match e with
    | .sort lvl =>
      return .sort lvl.toNat
    | .mdata _ e' =>
        abstractTypeLit e'
    | .app .. =>
        let fn := e.getAppFn.consumeMData
        let args := e.getAppArgs
        -- This might break!!
        let (implArgs, explArgs) ← liftM <| sortAppArgsWithTypes fn args
        let partialAppFn := mkAppN fn implArgs
        let argLits ← explArgs.mapM fun (arg, domain) =>
          abstractTypeArgWithExpected arg domain
        return .typeHole (← getTypeIdx partialAppFn) argLits
    | .fvar fvarId =>
        let s ← get
        if let some pair := s.vars.get? fvarId then
          return .var pair.1
        else if ← liftM <| isPropSafe e then
          return .opHole (← getOpIdx e).1 #[]
        else
          return .typeHole (← getTypeIdx e) #[]
    | .const .. =>
        let ty ← liftM <| whnf (← inferType e)
        if ty.isSort || ty.isForall then
          return .typeHole (← getTypeIdx e) #[]
        else
          return .const (← getConstIdx e).1
    | .lit .. =>
        return .const (← getConstIdx e).1
    | .mvar .. | .bvar .. | .lam .. | .forallE .. | .letE .. | .proj .. =>
        throwError m!"Unsupported in type literal abstraction: {e}"

  partial def abstractTypeArg (e : Expr) : AbstractM tempLit := do
    let e := e.consumeMData
    match e with
    | .sort .. => abstractTypeLit e
    | .fvar fvarId =>
        let s ← get
        match s.vars.get? fvarId with
        | some pair => return .var pair.1
        | none => abstractTypeLit e
    | _ =>
        let ty ← liftM <| whnf (← inferType e)
        if ty.isSort then
          abstractTypeLit e
        else
          abstractTerm e

  partial def abstractTypeArgWithExpected (e : Expr) (expectedType : Expr) : AbstractM tempLit := do
    let expectedType ← liftM <| whnf expectedType
    if expectedType.isSort then
      abstractTypeLit e
    else
      match e.consumeMData with
      | .fvar fvarId =>
          return .var (← getVarIdxWithType fvarId expectedType).1
      | _ =>
          abstractTerm e

  partial def abstractType (e : Expr) : AbstractM tempExpr := do
    let e := e.consumeMData
    if ← liftM <| isPropSafe e then
      return ← abstractProp e
    match e with
    | .forallE name type body bi =>
        withIgnoredLocal name bi type fun fvar => do
          let lhs ←
            if ← liftM <| isProp type then
              abstractProp type
            else
              abstractType type
          let rhs ← abstractType (body.instantiate1 fvar)
          return .bin .imp lhs rhs
    | .mdata _ e' =>
        abstractType e'
    | .sort .. | .fvar .. | .const .. | .app .. | .lit .. =>
        return .lit (← abstractTypeLit e)
    | .mvar .. | .bvar .. | .lam .. | .letE .. | .proj .. =>
        throwError m!"Unsupported in type abstraction: {e}"
end

partial def abstractContext : AbstractM (List (tempLit × tempExpr)) := do
  let rec processLoop (processedTypes : List Expr) (processedVars : List FVarId)
                      (processedConsts : List Expr) (processedOps : List Expr)
                      (result : List (tempLit × tempExpr)) :
      AbstractM (List (tempLit × tempExpr)) := do

    let s ← get

    let newTypes := s.simpleTypes.toList.filter (fun (ty, _) => !processedTypes.contains ty)
    let newVars := s.vars.toList.filter (fun (id, _) => !processedVars.contains id)
    let newConsts := s.consts.toList.filter (fun (expr, _) => !processedConsts.contains expr)
    let newOps := s.ops.toList.filter (fun (expr, _) => !processedOps.contains expr)

    if newTypes.isEmpty && newVars.isEmpty && newConsts.isEmpty && newOps.isEmpty then
      return result

    let mut currentResult := result
    let mut nextTypes := processedTypes
    let mut nextVars := processedVars
    let mut nextConsts := processedConsts
    let mut nextOps := processedOps

    for (ty, idx) in newTypes do
      let absTy ← abstractType (← Lean.Meta.inferType ty)
      currentResult := currentResult ++ [(.typeHole idx #[], absTy)]
      nextTypes := ty :: nextTypes

    for (fvarId, (idx, ty)) in newVars do
      let absTy ← abstractType ty
      currentResult := currentResult ++ [(.var idx, absTy)]
      nextVars := fvarId :: nextVars

    for (expr, (idx, ty)) in newConsts do
      let absTy ← abstractType ty
      currentResult := currentResult ++ [(.const idx, absTy)]
      nextConsts := expr :: nextConsts

    for (expr, (idx, ty)) in newOps do
      let absTy ← abstractType ty
      currentResult := currentResult ++ [(.opHole idx #[], absTy)]
      nextOps := expr :: nextOps

    processLoop nextTypes nextVars nextConsts nextOps currentResult
  processLoop [] [] [] [] []

partial def topologicalSort (remaining : List (tempLit × tempExpr))
  (sorted : List (tempLit × tempExpr) := []) : Except String (List (tempLit × tempExpr)) :=
  if remaining.isEmpty then
    return sorted
  else let readyOpt := remaining.find? fun (lit, typeExpr) =>
    remaining.all fun (otherLit, _) =>
      if lit == otherLit then
        true
      else
        !(typeExpr.contains otherLit)
  match readyOpt with
  | some readyElem =>
      let nextRemaining := remaining.filter (fun (l, _) => l != readyElem.1)
      topologicalSort nextRemaining (sorted ++ [readyElem])
  | none =>
      Except.error "Circular dependency detected in the extracted context!"

partial def abstractTypedTemplate (e : Expr) : AbstractM template := do
  let e := e.consumeMData
  match e with
  | .forallE name type body bi =>
      let typeIsProp ←
        try
          liftM <| isProp type
        catch ex =>
          throwError m!"Failed to classify theorem binder {name} : {repr type}\n{ex.toMessageData}"
      if typeIsProp then
        let statement ← abstractProp e
        let ctx ← abstractContext
        match (topologicalSort ctx []) with
        | Except.error msg => throwError m!"{msg}"
        | Except.ok sortedCtx =>
          return { ctx := sortedCtx, statement := statement }
      else if bi == BinderInfo.default then
        withAbstractedVar name bi type fun _idx fvar => do
          abstractTypedTemplate (body.instantiate1 fvar)
      else
        withIgnoredLocal name bi type fun fvar => do
          abstractTypedTemplate (body.instantiate1 fvar)
  | _ =>
      let statement ← abstractProp e
      let ctx ← abstractContext
      match (topologicalSort ctx []) with
      | Except.error msg => throwError m!"{msg}"
      | Except.ok sortedCtx =>
        return { ctx := sortedCtx, statement := statement }

-- elab tk:"#test_typed_abs " id:ident : command => runTermElabM fun _ => do
--   let name ← resolveGlobalConstNoOverload id
--   let info ← getConstInfo name
--   let type ← instantiateMVars info.type
--   let (t, _) ← (abstractTypedTemplate type).run {}
--   let stx ← delabExpr t.statement
--   withRef tk <| logInfo m!"\n{t.ctx}\n{stx}"

end TypedAbstraction

-- #test_typed_abs Fin.exists_iff
-- #test_typed_abs Function.comp_id
-- #test_typed_abs Nat.add_div
