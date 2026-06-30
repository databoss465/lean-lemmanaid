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
  | sort : Option Nat → tempLit
deriving Repr, BEq, Hashable, ToExpr

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
  | .sort (some idx) => Name.mkSimple s!"Sort{idx}"
  | .sort none => Name.mkSimple s!"Sort_u"

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
  | .sort (some 0) =>
      s!"Prop"
  | .sort (some n) =>
      s!"Type {n}"
  | .sort none =>
      s!"Type u_1"

instance : ToString tempLit where
  toString := tempLit.toString

inductive tempUnOp
 | not
deriving BEq, Hashable, ToExpr

instance : ToString tempUnOp where
  toString
  | .not => "¬"

instance : Repr tempUnOp where
  reprPrec
  |.not, _ => "Not"

inductive tempBinOp
 | and |or | imp | iff
deriving BEq, Hashable, ToExpr

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
deriving BEq, Hashable, ToExpr

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
  | bind : tempBinder → Nat → tempExpr → tempExpr → tempExpr
deriving Repr, BEq, Hashable, ToExpr

partial def tempExpr.contains (expr : tempExpr) (lit : tempLit) : Bool :=
  match expr with
  | .lit l => l.contains lit
  | .eq l r => (l.contains lit) ∨ (r.contains lit)
  | .bin _ l r => (l.contains lit) ∨ (r.contains lit)
  | .un _ e => e.contains lit
  | .bind _ _ t e => (t.contains lit) ∨ (e.contains lit)

partial def tempExpr.toString : tempExpr → String
  | .lit l =>
      l.toString
  | .eq l₁ l₂ =>
      s!"({l₁} = {l₂})"
  | .un op e =>
      s!"{op} {e.toString}"
  | .bin op e₁ e₂ =>
      s!"{e₁.toString} {op} {e₂.toString}"
  | .bind b n t e =>
      s!"{b} {n} {t.toString} {e.toString}"

instance : ToString tempExpr where
  toString := tempExpr.toString

-- Syntax for templates

declare_syntax_cat temp_lit
declare_syntax_cat temp_lit_atom

-- An atom of template_stx literals is either an identifier or an id in parantheses
syntax ident : temp_lit_atom
syntax "(" temp_lit ")" : temp_lit_atom

-- A template_stx literal can either be one
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
      else if nameStr.startsWith "T" then
        let n ← stxCheck id "T"
        return tempLit.typeHole n #[]
      else if nameStr == "Sort_u" then
        return tempLit.sort none
      else if nameStr.startsWith "Sort" then
        let n ← stxCheck id "Sort"
        return tempLit.sort (some n)
      else if nameStr == "Prop" then
        return tempLit.sort (some 0)
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
        else if nameStr.startsWith "T" then
          let opIdx ← stxCheck id "T"
          let mut argExprs := #[]
          for arg in args do
            argExprs := argExprs.push (← elabAtom arg)
          return tempLit.typeHole opIdx argExprs
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
declare_syntax_cat template_stx

syntax temp_lit " = " temp_lit : template_stx              -- Equality propositions
syntax temp_lit : template_stx                             -- Some literals, can be lemmas (Relational propositions)

syntax:50 temp_unop template_stx:51 : template_stx              -- Not
syntax:35 template_stx:36 temp_binop template_stx:35 : template_stx     -- And/Or/Implies


syntax "(" template_stx ")" : template_stx                    -- Grouping

-- Represents the context for the lemma
declare_syntax_cat template_type
syntax template_stx : template_type
syntax template_type " → " template_type : template_type
syntax "Prop" : template_type
syntax "Type" : template_type
syntax "Sort " num : template_type

syntax temp_binder ident ": " template_type ", " template_stx:10 : template_stx     -- Forall/Exists
syntax temp_binder ident+ ": " template_type ", " template_stx:10 : template_stx

declare_syntax_cat template_ctx
syntax temp_lit " : " template_type : template_ctx

mutual
partial def elabTemp : Syntax → MetaM tempExpr
  | `(template_stx| $lit:temp_lit) => do
    let e ← elabLit lit
    match e with
    | .opHole _ _ =>
      return .lit e
    | .var _  | .const _=>
      throwErrorAt lit "Only operator applications can be Propositions"
    | _ => throwUnsupportedSyntax
  | `(template_stx| $lhs:temp_lit = $rhs:temp_lit) => do
    let lExpr ← elabLit lhs
    let rExpr ← elabLit rhs
    return .eq lExpr rExpr
  | `(template_stx| $lhs:template_stx $bin:temp_binop $rhs:template_stx) => do
      let binExpr ← elabBinOp bin
      let lExpr ← elabTemp lhs
      let rExpr ← elabTemp rhs
      return .bin binExpr lExpr rExpr
  | `(template_stx| $u:temp_unop $e:template_stx) => do
      let uExpr ← elabUnOp u
      let eExpr ← elabTemp e
      return .un uExpr eExpr

  | `(template_stx| $b:temp_binder $var:ident : $type:template_type , $e:template_stx) => do
      let binderExpr ← elabBinder b
      let varIdx ← stxCheck var "x"
      let eExpr ← elabTemp e
      let bType ← elabTempType type
      return .bind binderExpr varIdx bType eExpr
  | `(template_stx| $b:temp_binder $var:ident $vars:ident* : $type:template_type , $e:template_stx) => do
      let binderExpr ← elabBinder b
      let eExpr ← elabTemp e
      let varIdx ← stxCheck var "x"
      let varsIdx ← vars.mapM (stxCheck · "x")
      let bType ← elabTempType type
      let inner ← varsIdx.foldrM (fun idx pred ↦ return tempExpr.bind binderExpr idx bType pred) eExpr
      return .bind binderExpr varIdx bType inner
  | `(template_stx| ($e:template_stx)) =>
      elabTemp e
  | _ => throwUnsupportedSyntax


partial def elabTempType : Syntax → MetaM tempExpr
  | `(template_type| $t:template_stx) => elabTempTypeExpr t
  | `(template_type| $lhs:template_type → $rhs:template_type) =>
      return .bin .imp (← elabTempType lhs) (← elabTempType rhs)
  | `(template_type| Prop) => return .lit (.sort (some 0))
  | `(template_type| Type) => return .lit (.sort (some 1))
  | `(template_type| Sort $n:num) => return .lit (.sort (some n.getNat))
  | _ => throwUnsupportedSyntax

-- Permissive version: accepts any tempLit (not just opHole), recurses via elabTempType
partial def elabTempTypeExpr : Syntax → MetaM tempExpr
  | `(template_stx| $lit:temp_lit) => return .lit (← elabLit lit)
  | `(template_stx| $lhs:temp_lit = $rhs:temp_lit) =>
      return .eq (← elabLit lhs) (← elabLit rhs)
  | `(template_stx| $lhs:template_stx $bin:temp_binop $rhs:template_stx) => do
      return .bin (← elabBinOp bin) (← elabTempTypeExpr lhs) (← elabTempTypeExpr rhs)
  | `(template_stx| $u:temp_unop $e:template_stx) =>
      return .un (← elabUnOp u) (← elabTempTypeExpr e)
  | `(template_stx| $b:temp_binder $var:ident : $type:template_type, $e:template_stx) => do
      return .bind (← elabBinder b) (← stxCheck var "x") (← elabTempType type) (← elabTempTypeExpr e)
      -- May need support for multi-binding. Subject to Mathlib testing.
  | `(template_stx| ($e:template_stx)) => elabTempTypeExpr e
  | _ => throwUnsupportedSyntax
end

-- Elaborates a single context entry into a (tempLit × tempExpr) pair
def elabTempCtx :  TSyntax `template_ctx → MetaM (tempLit × tempExpr)
  | `(template_ctx| $lit:temp_lit : $ty:template_type) =>
      return (← elabLit lit, ← elabTempType ty)
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

mutual
partial def delabType : tempExpr → MetaM (TSyntax `template_type)
  | .bin .imp l r => do
    `(template_type| $(← delabType l):template_type → $(← delabType r):template_type)
  | e => do
    `(template_type| $(← delabExpr e):template_stx)

partial def delabExpr : tempExpr → MetaM (TSyntax `template_stx)
  | .lit l => do
    let stx ← delabLit l
    `(template_stx| $stx:temp_lit)
  | .eq l r => do
    let lStx ← delabLit l
    let rStx ← delabLit r
    `(template_stx| $lStx:temp_lit = $rStx:temp_lit)
  | .un _ e => do
    let stx ← delabExpr e
    `(template_stx| ¬ $stx:template_stx)
  | .bin op l r => do
    let lStx ← delabExpr l
    let rStx ← delabExpr r
    match op with
    | .and => `(template_stx| $lStx:template_stx ∧ $rStx:template_stx)
    | .or =>  `(template_stx| $lStx:template_stx ∨ $rStx:template_stx)
    | .imp =>  `(template_stx| $lStx:template_stx → $rStx:template_stx)
    | .iff => `(template_stx| $lStx:template_stx ↔ $rStx:template_stx)
  | .bind op idx t e => do
    let name := (tempLit.var idx).mkNameIdent
    let type ← delabType t
    let body ← delabExpr e
    match op with
    | .forall => `(template_stx| ∀ $name:ident : $type:template_type, $body:template_stx)
    | .exists => `(template_stx| ∃ $name:ident : $type:template_type, $body:template_stx)
end

structure Template where
  ctx : List (tempLit × tempExpr)
  statement : tempExpr
deriving Repr, BEq, ToExpr

abbrev Template.addContext (T : Template) (t : (tempLit × tempExpr)) := {T with ctx := T.ctx.insert t}
abbrev Template.addContext' (T : Template) (ts : List (tempLit × tempExpr)) := {T with ctx := ts ++ T.ctx}
abbrev Template.setStatement (T : Template) (stx : TSyntax `template_stx) := do
  let st ← elabTemp stx
  return {T with statement := st}
