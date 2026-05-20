import Lean
open Lean Meta
-- set_option pp.all true

#eval show MetaM Unit from do
  let natType := mkConst ``Nat
  withLocalDecl `x .default natType fun x => do
  withLocalDecl `y .default natType fun y => do
    let f := mkConst `f
    let e := mkApp2 f x y
    IO.println s!"Original Expression: {e}"
    let absA := e.abstract #[x, y]
    IO.println s!"Abstracted with #[x, y]: {absA}"
    let absB := e.abstract #[y, x]
    IO.println s!"Abstracted with #[y, x]: {absB}"

open Lean Meta Elab Command Term

def abstractTemplate (e : Expr) : MetaM (Array FVarId × Expr) := do
  let fvarState := Lean.collectFVars {} e
  let fvarIds := fvarState.fvarIds
  let fvars := fvarIds.map mkFVar
  let absExpr := e.abstract fvars
  return (fvarIds, absExpr)

def fvarSorter (e : Expr) : MetaM (Array FVarId × Array FVarId) := do
  let fvarState := collectFVars {} e
  let fvarIds := fvarState.fvarIds
  let mut vars : Array FVarId := #[]
  let mut others : Array FVarId := #[]
  for fvarId in fvarIds do
    let fvar := mkFVar fvarId
    let fvarType ← instantiateMVars (← inferType fvar)
    if fvarType.isSort then
      others := others.push fvarId
    else if fvarType.isForall then
      others := others.push fvarId
    else
      vars := vars.push fvarId
  return (vars, others)

def abstractTemplate'(e : Expr) : MetaM ( Expr) := do
  let (_, others) ← fvarSorter e
  let fvars := others.map mkFVar
  let absExpr := e.abstract fvars
  return absExpr

elab "#abstract " t:term : command => runTermElabM fun _ => do
  let e' ← elabTerm t none
  let e ← instantiateMVars e'
  let (fvarIds, absExpr) ← abstractTemplate e
  IO.println s!"{absExpr}"
  logInfo m!"{fvarIds.size} free variables: {fvarIds.map (mkFVar ·)}\nOriginal: {e}\nAbstracted: {absExpr}"

elab "#abstract_less " t:term : command => runTermElabM fun _ => do
  let e' ← elabTerm t none
  let e ← instantiateMVars e'
  let absExpr ← abstractTemplate' e
  IO.println s!"{absExpr}"
  logInfo m!"Abstracted: {absExpr}"

-- elab "#inst " e:Expr : command => runTermElabM fun _ => do

section Abstraction
variable {α : Type} [Add α] [Mul α] (f : α → α → α) (g : α → α) (x y z : α) (p₁ p₂ : Prop)

#abstract f (f x y) z
#abstract_less f (f x y) z

#abstract f x y = f y x
#abstract_less f x y = f y x

#abstract g (g x) = x
#abstract_less g (g x) = x

#abstract p₁ ∧ p₂
#abstract ¬ p₁
#abstract ¬ p₁ ∨ p₂

-- Possible Problem with this
#abstract x + y = y + x
#abstract_less x + y = y + x

#abstract ∀ x, g x = y
#abstract ∃ x, g x = x
end Abstraction

#eval show MetaM Unit from do
  let info ← getConstInfo ``Rat.add_comm
  IO.println s!"{info.type}"

elab "#show " id:ident : command => runTermElabM fun _ ↦ do
  let name ← resolveGlobalConstNoOverload id
  let info ← getConstInfo name
  IO.println s!"{info.type}"

elab "#show_and_abstract " id:ident : command => runTermElabM fun _ ↦ do
  let name ← resolveGlobalConstNoOverload id
  let info ← getConstInfo name
  Lean.Meta.forallTelescope info.type fun _ body ↦ do
    let (_, absExpr) ← abstractTemplate body
    IO.println s!"\n{absExpr}"
    -- logInfo m!"{fvars.size} free variables: {fvarIds.map (mkFVar ·)}\nOriginal: {body}\nAbstracted: {absExpr}"

#show Nat.add_comm
#check Nat.mul_comm
#show_and_abstract Nat.add_comm
#show_and_abstract Vector.add_comm

elab "#inst" bang:("!")? t:term "with" "#[" args:term,* "]" : command =>
  runTermElabM fun _ => do
  let e ← instantiateMVars (← elabTerm t none)

  let useBang := bang.isSome

  let (arity, template) ← if useBang then
    let (vars, others) ← fvarSorter e                         -- Sorts variables
    let e' ← Lean.Meta.mkForallFVars (vars.map Expr.fvar) e   -- Makes the variables to forall
    let template ← abstractTemplate' e'                       -- Then all fvar -> bvar
    pure (others.size, template)
  else
    let (fvarIds, template) ← abstractTemplate e              -- Every fvar -> bvar
    pure (fvarIds.size, template)

  logInfo m!"Template : {template}"

  let mut subst : Array Expr := #[]
  for arg in args.getElems do
    let argExpr ← elabTerm arg none
    subst := subst.push argExpr

  if subst.size != arity then
    throwError m!"Arity mismatch! Template has {arity} variables, but input has {subst.size} arguments."

  let result := template.instantiateRev subst
  try
    check result
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let finalResult ← instantiateMVars result
    let abstractResult ← Lean.Meta.abstractMVars finalResult
    let finalTheorem := abstractResult.expr
    let thm ← Lean.Meta.lambdaTelescope finalTheorem fun fvars body => do
      Lean.Meta.mkForallFVars fvars body
    logInfo m!"{thm}"
    IO.println s!"{thm}"
  catch ex =>
    logInfo m!"{ex.toMessageData}"

-- variable (k m n : Nat) (p q : Int)
variable {α : Type}(f : α → α → α) (g : α → α) (x y z : α)

-- #inst f x y = f y x with #[_, HMul.hMul, m, n]
#inst! f x y = f y x with #[Nat, HMul.hMul]
#check Nat.mul_comm
-- Need forall instead of variables here

-- #inst f x y = f y x with #[Nat, HAdd.hAdd, m, n]
#inst! f x y = f y x with #[Nat, HAdd.hAdd]
#check Nat.add_comm

-- #inst f x (f y z) = f (f x y) z with #[Nat, HMul.hMul, k, m, n]
#inst! f x (f y z) = f (f x y) z with #[Nat, HMul.hMul]
#check Nat.mul_assoc


#abstract g (f x y) = f (g x) (g y)
-- #inst g (f x y) = f (g x) (g y) with #[Int, Neg.neg, HAdd.hAdd, p, q]
#inst! g (f x y) = f (g x) (g y) with #[Int, Neg.neg, HAdd.hAdd]
#check Int.neg_add

-- #inst f x y = f y x with #[Vector _ _, HAdd.hAdd, u, v]
#inst! f x y = f y x with #[Vector Nat _, HAdd.hAdd]

#inst f x y = y with #[Int, HMul.hMul, 1, _]
#show Int.one_mul
