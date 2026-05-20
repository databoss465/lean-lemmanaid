import Lean
open Lean Meta Elab Command Term

def stxCheck (id : Syntax) (pfx : String) : MetaM Nat := do
  let stx := id.getId.toString
  let validPrefix := stx.startsWith pfx
  let validLength := stx.length > pfx.length
  let validSuffix := (stx.drop pfx.length).all Char.isDigit

  if not (validPrefix && validLength && validSuffix) then
    throwErrorAt id s!"Invalid identifier '{stx}': expected '{pfx}' followed by digits"

  return (stx.drop pfx.length).toNat!

-- Abstract Syntax Tree

inductive tempLit
  | var : Nat → tempLit
  | opHole : Nat → Array tempLit → tempLit
  | typeHole : Nat → tempLit
deriving Repr

inductive tempUnOp
 | not

instance : ToString tempUnOp where
  toString
  | .not => "not"

instance : Repr tempUnOp where
  reprPrec
  |.not, _ => "¬"

inductive tempBinOp
 | and |or | imp

instance : ToString tempBinOp where
  toString
    | .and => "and"
    | .or  => "or"
    | .imp => "imp"

-- 2. The Pretty Printer (What #eval sees)
instance : Repr tempBinOp where
  reprPrec
    | .and, _ => "∧"
    | .or,  _ => "∨"
    | .imp, _ => "→"

inductive tempBinder
  | forallBind | existsBind

instance : Repr tempBinder where
  reprPrec
  | .forallBind, _ => "∀"
  | .existsBind, _ => "∃"


inductive tempExpr
  | lit : tempLit → tempExpr
  | eq : tempLit → tempLit → tempExpr
  | un : tempUnOp → tempExpr → tempExpr
  | bin : tempBinOp → tempExpr → tempExpr → tempExpr
  | bind : tempBinder → Nat → tempExpr → tempExpr
deriving Repr

structure template where
  opHoles : Array Nat
  vars : Array Nat
  statement : tempExpr

-- Syntax for templates

declare_syntax_cat temp_lit
declare_syntax_cat temp_lit_atom

-- An atom of template literals is either an identifier or an id in parantheses
syntax ident : temp_lit_atom
syntax "(" temp_lit ")" : temp_lit_atom

-- A template literal can either be one
syntax temp_lit_atom : temp_lit
syntax temp_lit_atom temp_lit_atom+ : temp_lit

-- Elaborating Literals
-- MIGHT WANT TO REWRITE THIS!!

mutual    -- Functions that call each other
/- Function to elaborate atoms, i.e. x1, (x1), etc.. -/
  partial def elabAtom (stx : Syntax) : MetaM Expr := do
    match stx with
    | `(temp_lit_atom| $id:ident) =>
      let nameStr := id.getId.toString
      -- If it is x"num" then make it a var
      if nameStr.startsWith "x" then
        let k ← stxCheck id "x"
        mkAppM ``tempLit.var #[mkNatLit k]

      -- H"num" -> Operator Hole
      else if nameStr.startsWith "H" then
        let n ← stxCheck id "H"
        let emptyArray ← mkAppM ``Array.empty #[.const ``tempLit []]
        mkAppM ``tempLit.opHole #[mkNatLit n, emptyArray]

      -- T"num" -> Type hole
      else if nameStr.startsWith "T" then
        let n ← stxCheck id "T"
        mkAppM ``tempLit.typeHole #[mkNatLit n]

      else
        throwErrorAt id s!"Unknown Lemmanaid identifier prefix for '{nameStr}'. Expected x, H, or T."

    -- If there's a paranthesis
    | `(temp_lit_atom| ( $inner:temp_lit ) ) => elabLit inner
    | _ => throwUnsupportedSyntax

  partial def elabLit (stx : Syntax) : MetaM Expr := do
    match stx with
    | `(temp_lit| $atm:temp_lit_atom) => elabAtom atm
    | `(temp_lit| $fnAtom:temp_lit_atom $args:temp_lit_atom*) => do
      match fnAtom with
      | `(temp_lit_atom| $id:ident) =>
        let nameStr := id.getId.toString
        if nameStr.startsWith "H" then
          let opIdx ← stxCheck id "H"
          let mut argExprs := #[]
          for arg in args do
            argExprs := argExprs.push (← elabAtom arg)
          let listExpr ← mkListLit (.const ``tempLit []) argExprs.toList
          let arrExpr ← mkAppM ``List.toArray #[listExpr]

          -- Scrutinize this later
          mkAppM ``tempLit.opHole #[mkNatLit opIdx, arrExpr]
        else
          throwErrorAt id "Application head must be an operator starting with 'H' (e.g., H1)"

      | _ => throwErrorAt fnAtom "Application head cannot be a complex expression. Use a raw operator."
    | _ => throwUnsupportedSyntax
end

elab "test_tempLit " l:temp_lit : term => elabLit l

#eval test_tempLit x1
#eval test_tempLit H1 x1 x2
#eval test_tempLit H1 (H2 x1 x2) (H3 x2 x1 x3)
#eval test_tempLit T5

-- Elaborating Expressions

declare_syntax_cat temp_unop
syntax "not " : temp_unop
syntax "¬ " : temp_unop

def elabUnOp : Syntax → MetaM Expr
  | `(temp_unop| not) => return .const ``tempUnOp.not []
  | _ => throwUnsupportedSyntax

declare_syntax_cat temp_binop

syntax "and" : temp_binop
syntax " ∧ " : temp_binop

syntax "or"  : temp_binop
syntax " ∨ " : temp_binop

syntax " imp " : temp_binop
syntax "→" : temp_binop

macro_rules
| `(temp_unop| ¬)  => `(temp_unop| not)

  | `(temp_binop| ∧)  => `(temp_binop| and)
  | `(temp_binop| ∨)  => `(temp_binop| or)
  | `(temp_binop| →)  => `(temp_binop| imp)

def elabBinOp : Syntax → MetaM Expr
  | `(temp_binop| and) | `(temp_binop| ∧) => return .const ``tempBinOp.and []
  | `(temp_binop| or)  | `(temp_binop| ∨)=> return .const ``tempBinOp.or []
  | `(temp_binop| imp) | `(temp_binop| →)=> return .const ``tempBinOp.imp []
  | _ => throwUnsupportedSyntax

declare_syntax_cat temp_binder
syntax "forall " : temp_binder
syntax "∀ " : temp_binder

syntax "exists " : temp_binder
syntax "∃ " : temp_binder

def elabBinder : Syntax → MetaM Expr
  | `(temp_binder| forall) | `(temp_binder| ∀) => return .const ``tempBinder.forallBind []
  | `(temp_binder| exists) | `(temp_binder| ∃)=> return .const ``tempBinder.existsBind []
  | _ => throwUnsupportedSyntax

-- Represents a "lemma" which is a proposition
declare_syntax_cat temp_expr

syntax temp_lit " = " temp_lit : temp_expr              -- Equality propositions
syntax temp_lit : temp_expr                             -- Some literals, can be lemmas (Relational propositions)

syntax temp_unop temp_expr : temp_expr                  -- Not
syntax temp_expr temp_binop temp_expr : temp_expr       -- And/Or/Implies
syntax temp_binder ident ", " temp_expr : temp_expr     -- Forall/Exists

syntax "(" temp_expr ")" : temp_expr                    -- Grouping

partial def elabExpr : Syntax → MetaM Expr
  | `(temp_expr| $lit:temp_lit) => do
    let e ← elabLit lit
    if e.isAppOf ``tempLit.opHole then
      mkAppM ``tempExpr.lit #[e]
    else
      throwErrorAt lit "Only operator applications can be Propositions"
  | `(temp_expr| $lhs:temp_lit = $rhs:temp_lit) => do
    let lExpr ← elabLit lhs
    let rExpr ← elabLit rhs
    mkAppM ``tempExpr.eq #[lExpr, rExpr]
  -- | `(temp_expr| $rel:ident $args:temp_lit_atom*) => do
  --   let nameStr := rel.getId.toString
  --   if nameStr.startsWith "H" then
  --     sorry
  --   else
  --     throwErrorAt rel "Relational holes are operators, must start with 'H' (e.g., H1)"
  | `(temp_expr| $u:temp_unop $e:temp_expr) => do
      let uExpr ← elabUnOp u
      let eExpr ← elabExpr e
      mkAppM ``tempExpr.un #[uExpr, eExpr]
  | `(temp_expr| $lhs:temp_expr $bin:temp_binop $rhs:temp_expr) => do
      let binExpr ← elabBinOp bin
      let lExpr ← elabExpr lhs
      let rExpr ← elabExpr rhs
      mkAppM ``tempExpr.bin #[binExpr, lExpr, rExpr]
  | `(temp_expr| $b:temp_binder $var:ident , $e:temp_expr) => do
      let binderExpr ← elabBinder b
      let varIdx ← stxCheck var "x"
      let eExpr ← elabExpr e
      mkAppM ``tempExpr.bind #[binderExpr, mkNatLit varIdx, eExpr]
  | `(temp_expr| ($e:temp_expr)) =>
    elabExpr e
  | _ => throwUnsupportedSyntax

elab "test_tempExpr " e:temp_expr : term => elabExpr e

#eval test_tempExpr x1 = H1 x2
#eval test_tempExpr H1 x1 x2
#eval test_tempExpr H1 x1 x2 = H1 x2 x1

-- #eval test_tempExpr ¬ (H1 x1 = x1)
#eval test_tempExpr (x1 = x2) ∧ (x2 = x3)
#eval test_tempExpr H1 x1 x2 = x1 ∨ H1 x1 x2 = x2

#eval test_tempExpr ∀ x1, x1 = x1

#eval test_tempExpr ∀ x1,∀ x2, H1 x1 x2 → H2 x1 x2

/-
TODO:
(Major)
1. Type inference => given T : template, return T' : typedTemplate
2. Context creation => given T' : typedTemplate create a local context with those variables (To be used in #inst)
(Minor fixes)
3. #abstract doesn't abstract the structure of typeclasses
4. #inst! ... with requires a fixed order of arguments.. can that be relaxed by writing an intelligent filler?
-/
