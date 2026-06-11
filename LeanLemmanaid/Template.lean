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


def mkVarName (idx : Nat) := Name.mkSimple s!"x{idx}"
def mkConstName (idx : Nat) := Name.mkSimple s!"c{idx}"
def mkOpName (idx : Nat) := Name.mkSimple s!"H{idx}"
def mkTypeName (idx : Nat) := Name.mkSimple s!"T{idx}"

-- Abstract Syntax Tree

inductive tempLit
  | const : Nat → tempLit
  | var : Nat → tempLit
  | opHole : Nat → Array tempLit → tempLit
  | typeHole : Nat → Array tempLit → tempLit
  | sort : Nat → tempLit
deriving Repr, BEq, Hashable

partial def tempLit.contains (t : tempLit) (l : tempLit) : Bool :=
  match t with
  | l'@(.const ..) | l'@(.var ..) |l'@(.sort ..) => l' == l
  | .opHole idx args =>
      (match l with | .opHole idx' _ => idx == idx' | _ => False) ||
      args.any (fun arg => arg.contains l)
  | .typeHole idx args =>
      (match l with | .typeHole idx' _ => idx == idx' | _ => False) ||
     args.any (fun arg => arg.contains l)

def tempLit.mkName (l : tempLit) :=
  match l with
  | .const idx => Name.mkSimple s!"c{idx}"
  | .var idx => Name.mkSimple s!"x{idx}"
  | .opHole idx _ => Name.mkSimple s!"H{idx}"
  | .typeHole idx _ => Name.mkSimple s!"T{idx}"
  | .sort idx => Name.mkSimple s!"Sort{idx}"

abbrev tempLit.mkNameIdent (l : tempLit) := mkIdent (l.mkName)

partial def tempLit.toString : tempLit → String
  | .const n =>
      s!"c{n}"
  | .var n =>
      s!"x{n}"
  | .opHole n args =>
      if args.isEmpty then
        s!"H{n}"
      else
        s!"H{n} {" ".intercalate (args.toList.map tempLit.toString)}"
  | .typeHole n args =>
      if args.isEmpty then
        s!"T{n}"
      else
        s!"T{n} {" ".intercalate (args.toList.map tempLit.toString)}"
  | .sort n =>
      s!"Type {n}"

instance : ToString tempLit where
  toString := tempLit.toString

inductive tempUnOp
 | not
deriving BEq, Hashable

instance : ToString tempUnOp where
  toString
  | .not => "¬"

instance : Repr tempUnOp where
  reprPrec
  |.not, _ => "Not"

inductive tempBinOp
 | and |or | imp | iff
deriving BEq, Hashable

instance : ToString tempBinOp where
  toString
    | .and => "∧"
    | .or  => "∨"
    | .imp => "→"
    | .iff => "↔"

instance : Repr tempBinOp where
  reprPrec
    | .and, _ => "And"
    | .or,  _ => "Or"
    | .imp, _ => "Imp"
    | .iff, _ => "Iff"


inductive tempBinder
  | forall | exists
deriving BEq, Hashable

instance : Repr tempBinder where
  reprPrec
  | .forall, _ => "Forall"
  | .exists, _ => "Exists"

instance : ToString tempBinder where
  toString
  | .forall => "∀"
  | .exists => "∃"


inductive tempExpr
  | lit : tempLit → tempExpr
  | eq : tempLit → tempLit → tempExpr
  | un : tempUnOp → tempExpr → tempExpr
  | bin : tempBinOp → tempExpr → tempExpr → tempExpr
  | bind : tempBinder → Nat → tempExpr → tempExpr
deriving Repr, BEq, Hashable

partial def tempExpr.contains (expr : tempExpr) (lit : tempLit) : Bool :=
  match expr with
  | .lit l => l.contains lit
  | .eq l r => (l.contains lit) ∨ (r.contains lit)
  | .bin _ l r => (l.contains lit) ∨ (r.contains lit)
  | .un _ e => e.contains lit
  | .bind _ _ e => e.contains lit

partial def tempExpr.toString : tempExpr → String
  | .lit l =>
      l.toString
  | .eq l₁ l₂ =>
      s!"({l₁} = {l₂})"
  | .un op e =>
      s!"{op} {tempExpr.toString e}"
  | .bin op e₁ e₂ =>
      s!"{tempExpr.toString e₁} {op} {tempExpr.toString e₂}"
  | .bind b n e =>
      s!"{b} {n}. {tempExpr.toString e}"

instance : ToString tempExpr where
  toString := tempExpr.toString

structure template where
  name : String := ""
  ctx : List (tempLit × tempExpr)
  statement : tempExpr

abbrev template.addContext (T : template) (t : (tempLit × tempExpr)) := T.ctx.insert t

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

mutual    -- Functions that call each other

/- Function to elaborate atoms, i.e. x1, (x1), etc.. -/
  partial def elabAtom (stx : Syntax) : MetaM tempLit := do
    match stx with
    | `(temp_lit_atom| $id:ident) =>
      let nameStr := id.getId.toString
      if nameStr.startsWith "x" then
        let k ← stxCheck id "x"
        return tempLit.var k
      else if nameStr.startsWith "c" then
        let k ← stxCheck id "c"
        return tempLit.const k
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

declare_syntax_cat temp_binop

syntax "and" : temp_binop
syntax " ∧ " : temp_binop

syntax "or"  : temp_binop
syntax " ∨ " : temp_binop

syntax " imp " : temp_binop
syntax " → " : temp_binop

syntax " iff " : temp_binop
syntax " ↔ " : temp_binop

def elabBinOp : Syntax → MetaM tempBinOp
  | `(temp_binop| and) | `(temp_binop| ∧) => return .and
  | `(temp_binop| or)  | `(temp_binop| ∨)=> return .or
  | `(temp_binop| imp) | `(temp_binop| →)=> return .imp
  | `(temp_binop| iff) | `(temp_binop| ↔)=> return .iff
  | _ => throwUnsupportedSyntax

declare_syntax_cat temp_unop
syntax "not " : temp_unop
syntax "¬" : temp_unop

def elabUnOp : Syntax → MetaM tempUnOp
  | `(temp_unop| not) | `(temp_unop| ¬) => return .not
  | _ => throwUnsupportedSyntax

declare_syntax_cat temp_binder
syntax "forall " : temp_binder
syntax "∀ " : temp_binder

syntax "exists " : temp_binder
syntax "∃ " : temp_binder

def elabBinder : Syntax → MetaM tempBinder
  | `(temp_binder| forall) | `(temp_binder| ∀) => return .forall
  | `(temp_binder| exists) | `(temp_binder| ∃)=> return .exists
  | _ => throwUnsupportedSyntax

-- Represents a "lemma" which is a proposition
declare_syntax_cat template

syntax temp_lit " = " temp_lit : template              -- Equality propositions
syntax temp_lit : template                             -- Some literals, can be lemmas (Relational propositions)

syntax:50 temp_unop template:51 : template              -- Not
syntax:35 template:36 temp_binop template:35 : template     -- And/Or/Implies
syntax temp_binder ident ", " template:10 : template     -- Forall/Exists
syntax temp_binder ident+ ", " template:10 : template

syntax "(" template ")" : template                    -- Grouping

partial def elabTemp : Syntax → MetaM tempExpr
  | `(template| $lit:temp_lit) => do
    let e ← elabLit lit
    match e with
    | .opHole _ _ =>
      return .lit e
    | .var _  | .const _=>
      throwErrorAt lit "Only operator applications can be Propositions"
    | _ => throwUnsupportedSyntax
  | `(template| $lhs:temp_lit = $rhs:temp_lit) => do
    let lExpr ← elabLit lhs
    let rExpr ← elabLit rhs
    return .eq lExpr rExpr
  | `(template| $lhs:template $bin:temp_binop $rhs:template) => do
      let binExpr ← elabBinOp bin
      let lExpr ← elabTemp lhs
      let rExpr ← elabTemp rhs
      return .bin binExpr lExpr rExpr
  | `(template| $u:temp_unop $e:template) => do
      let uExpr ← elabUnOp u
      let eExpr ← elabTemp e
      return .un uExpr eExpr

  | `(template| $b:temp_binder $var:ident , $e:template) => do
      let binderExpr ← elabBinder b
      let varIdx ← stxCheck var "x"
      let eExpr ← elabTemp e
      return .bind binderExpr varIdx eExpr
  | `(template| $b:temp_binder $var:ident $vars:ident* , $e:template) => do
      let binderExpr ← elabBinder b
      let eExpr ← elabTemp e
      let varIdx ← stxCheck var "x"
      let varsIdx ← vars.mapM (stxCheck · "x")
      let inner ← varsIdx.foldrM (fun idx pred ↦ return tempExpr.bind binderExpr idx pred) eExpr
      return .bind binderExpr varIdx inner
  | `(template| ($e:template)) =>
      elabTemp e
  | _ => throwUnsupportedSyntax

mutual
partial def delabAtom : tempLit → MetaM (TSyntax `temp_lit_atom)
  | t@(.var _) | t@(.const _) | t@(.sort _) =>
    `(temp_lit_atom| $(t.mkNameIdent):ident)
  | t@(.opHole ..) | t@(.typeHole ..) => do
    let inner ← delabLit t
    `(temp_lit_atom| ($inner:temp_lit))

partial def delabLit : tempLit → MetaM (TSyntax `temp_lit)
  | t@(.var _) | t@(.const _) | t@(.sort _) => do
    let stx ← delabAtom t
    `(temp_lit| $stx:temp_lit_atom)
  | t@(.opHole _ args) | t@(.typeHole _ args) => do
    let fn ← `(temp_lit_atom| $(t.mkNameIdent):ident)
    let argStx ← args.mapM delabAtom
    `(temp_lit| $fn:temp_lit_atom $argStx:temp_lit_atom*)
end

def delabExpr : tempExpr → MetaM (TSyntax `template)
  | .lit l => do
    let stx ← delabLit l
    `(template| $stx:temp_lit)
  | .eq l r => do
    let lStx ← delabLit l
    let rStx ← delabLit r
    `(template| $lStx:temp_lit = $rStx:temp_lit)
  | .un _ e => do
    let stx ← delabExpr e
    `(template| ¬ $stx:template)
  | .bin op l r => do
    let lStx ← delabExpr l
    let rStx ← delabExpr r
    match op with
    | .and => `(template| $lStx:template ∧ $rStx:template)
    | .or =>  `(template| $lStx:template ∨ $rStx:template)
    | .imp =>  `(template| $lStx:template → $rStx:template)
    | .iff => `(template| $lStx:template ↔ $rStx:template)
  | .bind op idx e => do
    let name := (tempLit.var idx).mkNameIdent
    let body ← delabExpr e
    match op with
    | .forall => `(template| ∀ $name:ident, $body:template)
    | .exists => `(template| ∃ $name:ident, $body:template)

elab tk:"#test_delab " t:template : command =>
  liftTermElabM do
    let e ← elabTemp t
    let t' ← delabExpr e
    withRef tk <| logInfo m!"original: {t}\ndelabbed: {t'}"

#test_delab ∀ x1 x2, H1 x1 x2 = H1 x2 x1 → ∀ x3 x4, H2 x3 x4 = H2 x4 x3
