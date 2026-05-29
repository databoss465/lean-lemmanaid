import Lean
import LeanLemmanaid.Template
import LeanLemmanaid.Unifier

open Lean Meta Elab Command Term

structure AbstractionState where
  nextVar : Nat := 1
  nextOp : Nat := 1
  vars : Std.HashMap FVarId Nat := {}
  ops : Std.HashMap Expr Nat := {}

abbrev AbstractionM := StateRefT AbstractionState MetaM

def getVarIdx (fvarId : FVarId) : AbstractionM Nat := do
  let s ← get
  match s.vars.get? fvarId with
  | some idx => return idx
  | none =>
      let idx := s.nextVar
      modify fun s => { s with
        nextVar := idx + 1
        vars := s.vars.insert fvarId idx
      }
      return idx

def getOpIdx (head : Expr) : AbstractionM Nat := do
  let head := head.consumeMData
  let s ← get
  match s.ops.get? head with
  | some idx => return idx
  | none =>
      let idx := s.nextOp
      modify fun s => { s with
        nextOp := idx + 1
        ops := s.ops.insert head idx
      }
      return idx

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
    (k : Nat → Expr → AbstractionM α) : AbstractionM α := do
  withLocalDecl name bi type fun fvar => do
    let idx ← getVarIdx fvar.fvarId!
    k idx fvar

def withIgnoredLocal {α : Type} (name : Name) (bi : BinderInfo) (type : Expr)
    (k : Expr → AbstractionM α) : AbstractionM α := do
  withLocalDecl name bi type k

mutual
  partial def abstractProp (e : Expr) : AbstractionM tempExpr := do
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
          return .lit (.opHole (← getOpIdx e) #[])
        else
          throwError m!"Expected proposition, got term variable {e}"
    | .mvar .. =>
        throwError m!"Unsupported metavariable in proposition abstraction: {e}"
    | .bvar .. =>
        throwError m!"Unsupported loose bound variable in proposition abstraction: {e}"
    | .lam .. =>
        throwError m!"Unsupported lambda in proposition abstraction: {e}"
    | .letE .. =>
        throwError m!"Unsupported let expression in proposition abstraction: {e}"
    | .mdata _ e' =>
        abstractProp e'
    | .lit .. | .const .. | .sort .. | .proj .. =>
        if ← liftM <| isProp e then
          return .lit (.opHole (← getOpIdx e) #[])
        else
          throwError m!"Expected proposition, got {e}"

  partial def abstractTerm (e : Expr) : AbstractionM tempLit := do
    let e := e.consumeMData
    match e with
    | .fvar fvarId =>
        if ← liftM <| isProp e then
          return .opHole (← getOpIdx e) #[]
        else
          return .var (← getVarIdx fvarId)
    | .app .. =>
        let fn := e.getAppFn.consumeMData
        let args := e.getAppArgs
        match fn with
        | .const ``Eq _ | .const ``Not _ | .const ``And _ | .const ``Or _ | .const ``Exists _ =>
            throwError m!"Logical proposition used as a term: {e}"
        | _ =>
            let explArgs ← liftM <| explicitAppArgs fn args
            let argLits ← explArgs.mapM abstractTerm
            return .opHole (← getOpIdx fn) argLits
    | .const .. =>
        return .opHole (← getOpIdx e) #[]
    | .mvar .. =>
        throwError m!"Unsupported metavariable in term abstraction: {e}"
    | .bvar .. =>
        throwError m!"Unsupported loose bound variable in term abstraction: {e}"
    | .lam .. =>
        throwError m!"Unsupported lambda in term abstraction: {e}"
    | .forallE .. =>
        throwError m!"Unsupported forall expression in term abstraction: {e}"
    | .letE .. =>
        throwError m!"Unsupported let expression in term abstraction: {e}"
    | .sort .. =>
        throwError m!"Unsupported sort in term abstraction: {e}"
    | .lit .. =>
        throwError m!"Unsupported literal in term abstraction: {e}"
    | .proj .. =>
        throwError m!"Unsupported projection in term abstraction: {e}"
    | .mdata _ e' =>
        abstractTerm e'
end

-- def buildTemplate (e : Expr) : MetaM tempExpr := do
--   let mut vars := 0
--   let mut Ops := 0
--   match e.consumeMData with
--   | .app .. => do
--     match e.getAppFn with
--     | .const ``Eq _ => do sorry
--     | .const ``And _ => do sorry
--     | .const ``Or _ => do sorry
--     | _ => do sorry
--   | .forallE _ _ _ _ => do sorry
--   | .fvar _ => do sorry
--   | _ => throwError m!"oops"

elab tk:"#test_abs " id:ident : command => runTermElabM fun _ => do
  let name ← resolveGlobalConstNoOverload id
  let info ← getConstInfo name
  let type ← instantiateMVars info.type
  let (template, _) ← (abstractProp type).run {}
  let stx ← delabExpr template
  withRef tk <| logInfo m!"{stx}"
