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
  --| typeHole : Nat → tempLit
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

-- instance : ToString tempBinOp where
--   toString
--     | .and => "and"
--     | .or  => "or"
--     | .imp => "imp"

instance : Repr tempBinOp where
  reprPrec
    | .and, _ => "And"
    | .or,  _ => "Or"
    | .imp, _ => "Imp"

inductive tempBinder
  | forallBind | existsBind

instance : Repr tempBinder where
  reprPrec
  | .forallBind, _ => "Forall"
  | .existsBind, _ => "Exists"


inductive tempExpr
  | lit : tempLit → tempExpr
  | eq : tempLit → tempLit → tempExpr
  | un : tempUnOp → tempExpr → tempExpr
  | bin : tempBinOp → tempExpr → tempExpr → tempExpr
  | bind : tempBinder → Nat → tempExpr → tempExpr
deriving Repr

-- structure template where
--   opHoles : Array Nat
--   vars : Array Nat
--   statement : tempExpr

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
  partial def elabAtom (stx : Syntax) : MetaM tempLit := do
    match stx with
    | `(temp_lit_atom| $id:ident) =>
      let nameStr := id.getId.toString
      if nameStr.startsWith "x" then
        let k ← stxCheck id "x"
        return tempLit.var k

      -- H"num" -> Operator Hole
      else if nameStr.startsWith "H" then
        let n ← stxCheck id "H"
        return tempLit.opHole n #[]

      else
        throwErrorAt id s!"Unknown Lemmanaid identifier prefix for '{nameStr}'. Expected x, H, or T."

    -- If there's a paranthesis
    | `(temp_lit_atom| ( $inner:temp_lit ) ) => elabLit inner
    | _ => throwUnsupportedSyntax

  partial def elabLit (stx : Syntax) : MetaM tempLit := do
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
          return tempLit.opHole opIdx argExprs
        else
          throwErrorAt id "Application head must be an operator starting with 'H' (e.g., H1)"

      | _ => throwErrorAt fnAtom "Application head cannot be a complex expression. Use a raw operator."
    | _ => throwUnsupportedSyntax
end

declare_syntax_cat temp_unop
syntax "not " : temp_unop
syntax "¬ " : temp_unop

def elabUnOp : Syntax → MetaM tempUnOp
  | `(temp_unop| not) => return .not
  | _ => throwUnsupportedSyntax

declare_syntax_cat temp_binop

syntax "and" : temp_binop
syntax " ∧ " : temp_binop

syntax "or"  : temp_binop
syntax " ∨ " : temp_binop

syntax " imp " : temp_binop
syntax "→" : temp_binop

def elabBinOp : Syntax → MetaM tempBinOp
  | `(temp_binop| and) | `(temp_binop| ∧) => return .and
  | `(temp_binop| or)  | `(temp_binop| ∨)=> return .or
  | `(temp_binop| imp) | `(temp_binop| →)=> return .imp
  | _ => throwUnsupportedSyntax

declare_syntax_cat temp_binder
syntax "forall " : temp_binder
syntax "∀ " : temp_binder

syntax "exists " : temp_binder
syntax "∃ " : temp_binder

def elabBinder : Syntax → MetaM tempBinder
  | `(temp_binder| forall) | `(temp_binder| ∀) => return .forallBind
  | `(temp_binder| exists) | `(temp_binder| ∃)=> return .existsBind
  | _ => throwUnsupportedSyntax

-- Represents a "lemma" which is a proposition
declare_syntax_cat template

syntax temp_lit " = " temp_lit : template              -- Equality propositions
syntax temp_lit : template                             -- Some literals, can be lemmas (Relational propositions)

syntax temp_unop template : template                  -- Not
syntax template temp_binop template : template       -- And/Or/Implies
syntax temp_binder ident ", " template : template     -- Forall/Exists

syntax "(" template ")" : template                    -- Grouping

partial def elabTemp : Syntax → MetaM tempExpr
  | `(template| $lit:temp_lit) => do
    let e ← elabLit lit
    match e with
    | .opHole _ _ =>
      return .lit e
    | .var _ =>
      throwErrorAt lit "Only operator applications can be Propositions"
  | `(template| $lhs:temp_lit = $rhs:temp_lit) => do
    let lExpr ← elabLit lhs
    let rExpr ← elabLit rhs
    return .eq lExpr rExpr
  | `(template| $u:temp_unop $e:template) => do
      let uExpr ← elabUnOp u
      let eExpr ← elabTemp e
      return .un uExpr eExpr
  | `(template| $lhs:template $bin:temp_binop $rhs:template) => do
      let binExpr ← elabBinOp bin
      let lExpr ← elabTemp lhs
      let rExpr ← elabTemp rhs
      return .bin binExpr lExpr rExpr
  | `(template| $b:temp_binder $var:ident , $e:template) => do
      let binderExpr ← elabBinder b
      let varIdx ← stxCheck var "x"
      let eExpr ← elabTemp e
      return .bind binderExpr varIdx eExpr
  | `(template| ($e:template)) =>
    elabTemp e
  | _ => throwUnsupportedSyntax

/-
TODO:
(Major)
1. Type inference => given T : template, return T' : typedTemplate
2. Context creation => given T' : typedTemplate create a local context with those variables (To be used in #inst)
(Minor fixes)
3. #abstract doesn't abstract the structure of typeclasses
4. #inst! ... with requires a fixed order of arguments.. can that be relaxed by writing an intelligent filler?
-/
