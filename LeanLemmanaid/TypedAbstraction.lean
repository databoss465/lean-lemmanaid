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
  boundVars : Std.HashSet Nat := {}

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

partial def stripNonExplicitBinders : Expr → Expr
  | .forallE n domain body .default =>
      .forallE n domain (stripNonExplicitBinders body) .default
  | .forallE _ _ body _ =>
      stripNonExplicitBinders (body.instantiate1 (.sort 0))  -- skip non-explicit, shift bvars
  | other => other

def getOpIdx (head : Expr) : AbstractM (Nat × Expr) := do
  let head := head.consumeMData
  let s ← get
  match s.ops.get? head with
  | some pair => return pair
  | none =>
      let idx ← getOpCount
      let ty := stripNonExplicitBinders (← inferType head)
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
arguments that should appear as template arguments.
Only *leading* implicit args (before the first explicit arg) are included in
`implMasked` and folded into the canonical `partialAppFn`. Instance-implicit args
that appear after the first explicit arg (e.g. the `[Decidable c]` in `@ite`) are
skipped from both arrays — they are dependent on explicit args and would produce an
ill-typed partial application if included in `implMasked`. Lean's typeclass inference
will reconstruct them at instantiation time. -/
partial def sortAppArgs (fn : Expr) (args : Array Expr) : MetaM (Array Expr × Array Expr) := do
  let mut fnType ← inferType fn
  let mut implMasked := #[]
  let mut expl := #[]
  let mut seenExplicit := false
  for arg in args do
    let t ← whnf fnType
    match t with
    | .forallE _ _ body bi =>
        if bi == BinderInfo.default then
          seenExplicit := true
          expl := expl.push arg
        else if !seenExplicit then
          implMasked := implMasked.push arg  -- only leading implicits go into partialAppFn
        -- instance-implicit args after the first explicit arg are skipped entirely
        fnType := body.instantiate1 arg
    | _ =>
        throwError m!"Cannot read application arity for {fn}; expected a function type, got {t}"
  return (implMasked, expl)

partial def sortAppArgsWithTypes (fn : Expr) (args : Array Expr) :
    MetaM (Array Expr × Array (Expr × Expr)) := do
  let mut fnType ← inferType fn
  let mut implMasked := #[]
  let mut expl := #[]
  let mut seenExplicit := false
  for arg in args do
    let t ← whnf fnType
    match t with
    | .forallE _ domain body bi =>
        if bi == BinderInfo.default then
          seenExplicit := true
          expl := expl.push (arg, domain)
        else if !seenExplicit then
          implMasked := implMasked.push arg
        -- instance-implicit args after the first explicit arg are skipped entirely
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

def withBoundVar {α : Type} (name : Name) (bi : BinderInfo) (type : Expr)
    (k : Nat → Expr → AbstractM α) : AbstractM α := do
  withLocalDecl name bi type fun fvar => do
    let (idx, _) ← getVarIdx fvar.fvarId!
    modify fun s => { s with boundVars := s.boundVars.insert idx }
    k idx fvar

def withIgnoredLocal {α : Type} (name : Name) (bi : BinderInfo) (type : Expr)
    (k : Expr → AbstractM α) : AbstractM α := do
  withLocalDecl name bi type k

def isPropSafe (e : Expr) : MetaM Bool := do
  try
    isProp e
  catch _ =>
    return false

/-- True if `e` mentions no *value-level* free variables: every fvar it contains is
either a type (its type is a `Sort`) or a typeclass instance (its type is a class).
Such an expression is a ground value — e.g. `(1 : G)`, which is `OfNat.ofNat G 1 inst`
and only "freely" mentions the abstracted type parameter `G` and its `Group` instance —
so it may be collapsed to a single constant even though it is not syntactically closed.
A genuine value variable (e.g. `a : G`) makes this return `false`, blocking collapse. -/
def hasNoValueFVars (e : Expr) : MetaM Bool := do
  let lctx ← getLCtx
  for fvarId in (Lean.collectFVars {} e).fvarIds do
    -- An fvar may be out of scope here: `abstractContext` re-abstracts stored types
    -- (e.g. `i < n`) after the binder that introduced `i` has closed. A dangling fvar is
    -- always a value variable that was abstracted earlier, so treat "not in scope" as
    -- blocking — never call `inferType` on it (that would throw "unknown free variable").
    let some decl := lctx.find? fvarId | return false
    let ty := decl.type
    if (← whnf ty).isSort then
      continue                         -- a type parameter (e.g. `G : Type`)
    if (← isClass? ty).isSome then
      continue                         -- a typeclass instance (e.g. `inst : Group G`)
    return false                       -- a genuine value variable (e.g. `a : G`)
  return true

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
                withBoundVar name bi type fun idx fvar => do
                  return .bind .exists idx (← abstractType type) (← abstractProp (body.instantiate1 fvar))
            | pred =>
                throwError m!"Expected existential predicate to be a lambda, got {pred}"
        | _ =>
            return .lit (← abstractTerm e)
    | .forallE name type body bi =>
        if ← liftM <| isProp type then
          return .bin .imp (← abstractProp type) (← abstractProp body)
        else if bi == BinderInfo.default then
          withBoundVar name bi type fun idx fvar => do
            return .bind .forall idx (← abstractType type) (← abstractProp (body.instantiate1 fvar))
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

    -- Collapse a ground value to a single constant. We allow the expression to mention
    -- type-parameter / instance fvars (e.g. the `G` in `(1 : G)`); only *value* fvars
    -- block the collapse. Mvars and loose bvars still disqualify.
    if !(e.hasMVar || e.hasLooseBVars) && (← liftM <| hasNoValueFVars e) then
      if !(← liftM <| isProp e) then
        let ty ← liftM <| whnf (← inferType e)
        if !ty.isForall && !ty.isSort then
          return .const (← getConstIdx e).1

    match e with
    | .fvar fvarId =>
        let s ← get
        let ty ← liftM <| whnf (← inferType e)
        if let some pair := s.vars.get? fvarId then
          return .var pair.1
        if ty.isForall then
          return .opHole (← getOpIdx e).1 #[]
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
            let (implArgs, explArgs) ← liftM <| sortAppArgsWithTypes fn args
            let partialAppFn := mkAppN fn implArgs
            -- Route each explicit arg through its expected domain: a `Sort`-typed argument
            -- (e.g. the `G` in `IsRightCancelMul G`) becomes a type hole, while ordinary
            -- value arguments stay term variables. Without this, a type passed as an
            -- explicit argument would be abstracted as a `.var` (`x1`) instead of `T1`.
            let argLits ← explArgs.mapM fun (arg, domain) =>
              abstractTypeArgWithExpected arg domain
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
      let propExpr ← abstractProp e
      match propExpr with
      | .lit l => return l                        -- reuses existing holes (H5, x1, etc.)
      | _ => return .opHole (← getOpIdx e).1 #[] -- compound prop, stay opaque
    match e with
    | .sort lvl =>
      return .sort lvl.toNat
    | .mdata _ e' =>
        abstractTypeLit e'
    | .app .. =>
        let fn := e.getAppFn.consumeMData
        let args := e.getAppArgs
        -- This might break!! Called it!
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
    if ← liftM <| isPropSafe e then
      let propExpr ← abstractProp e
      match propExpr with
      | .lit l => return l                         -- e.g. LE.le c (...) → reuses H5
      | _ => return .opHole (← getOpIdx e).1 #[]  -- e.g. a = b, A ∧ B → still opaque
    else
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
        if body.hasLooseBVar 0 && !(← liftM <| isProp type) then
          withBoundVar name bi type fun idx fvar => do
            return .bind .forall idx (← abstractType type) (← abstractType (body.instantiate1 fvar))
        else
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

    let newTypes := (s.simpleTypes.toList.filter (fun (ty, _) => !processedTypes.contains ty)).toArray.qsort (·.2 < ·.2) |>.toList
    let newVars := (s.vars.toList.filter (fun (id, pair) => !processedVars.contains id && !s.boundVars.contains pair.1)).toArray.qsort (·.2.1 < ·.2.1) |>.toList
    let newConsts := (s.consts.toList.filter (fun (expr, _) => !processedConsts.contains expr)).toArray.qsort (·.2.1 < ·.2.1) |>.toList
    let newOps := (s.ops.toList.filter (fun (expr, _) => !processedOps.contains expr)).toArray.qsort (·.2.1 < ·.2.1) |>.toList

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
  else
    -- An element is ready once every other element it depends on has been placed.
    let isReady := fun (lit, typeExpr) =>
      remaining.all fun (otherLit, _) =>
        if lit == otherLit then
          true
        else
          !(typeExpr.contains otherLit)
    -- A type-level hole (or sort). Among the ready elements we always prefer these
    -- so that types are emitted before value variables whenever no genuine
    -- dependency forces otherwise. This keeps value variables out of scope while a
    -- type hole is being instantiated, so an unfilled type hole (`_`) cannot capture
    -- a value variable when `abstractMVars` later generalizes it.
    let isTypeLike := fun (lit : tempLit) =>
      match lit with
      | .typeHole .. | .sort .. => true
      | _ => false
    let readyOpt :=
      match remaining.find? (fun e => isTypeLike e.1 && isReady e) with
      | some e => some e
      | none => remaining.find? isReady
    match readyOpt with
    | some readyElem =>
        let nextRemaining := remaining.filter (fun (l, _) => l != readyElem.1)
        topologicalSort nextRemaining (sorted ++ [readyElem])
    | none =>
        Except.error "Circular dependency detected in the extracted context!"

partial def abstractTypedTemplate (e : Expr) : AbstractM Template := do
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

end TypedAbstraction
