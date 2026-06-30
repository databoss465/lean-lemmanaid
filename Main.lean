import LeanLemmanaid

set_option pp.proofs true

/-
## Sanity Check
Testing examples that don't need Mathlib
-/
#check Nat.add_comm
template comm := Nat.add_comm
#show_template comm
template comm' := H1 x1 x2 = H1 x2 x1 where
  T1 : Type, x1 : T1, x2 : T1, H1 : T1 → T1 → T1
#show_template comm'
#instantiate comm with #[Nat, HAdd.hAdd]

#check Nat.add_add_add_comm
template super_comm := Nat.add_add_add_comm
#show_template super_comm
-- #inst_temp H1 (H1 x1 x2) (H1 x3 x4) = H1 (H1 x1 x3) (H1 x2 x4) with
  -- #[Nat, HAdd.hAdd]

#check Nat.add_assoc
template assoc := Nat.add_assoc
#show_template assoc
#instantiate assoc with #[Nat, HAdd.hAdd]

#check Nat.add_zero
#check Fin.add_zero
variable (n : Nat)
template right_id := Nat.add_zero
#show_template right_id
#instantiate right_id with #[Nat, 0, HAdd.hAdd]
#instantiate right_id with #[Fin (_+1), 0, HAdd.hAdd]
#instantiate right_id with #[Fin _, _, HAdd.hAdd]


#check Int.neg_add
template neg_distrib := Int.neg_add
#show_template neg_distrib
#instantiate neg_distrib with #[Int, HAdd.hAdd, Neg.neg]

#check Vector.add_comm
template depdt_comm := Vector.add_comm
#show_template depdt_comm
#instantiate depdt_comm with #[Int, Nat, Vector, HAdd.hAdd, HAdd.hAdd]

#check Nat.add_mul
template right_distrib := Nat.add_mul
#show_template right_distrib
#instantiate right_distrib with #[Nat, HAdd.hAdd, HMul.hMul]

#check Nat.add_div
template div_right_distrib := Nat.add_div
#show_template div_right_distrib
#instantiate div_right_distrib with #[Nat, 0, 1, LT.lt, HAdd.hAdd, HDiv.hDiv, HMod.hMod, LE.le, ite]

#check Nat.div_add_mod
template div_law := Nat.div_add_mod
#show_template div_law
#instantiate div_law with #[Nat, HDiv.hDiv, HMod.hMod, HAdd.hAdd, HMul.hMul]

#check Nat.eq_mul_of_div_eq_left
template mul_div := Nat.eq_mul_of_div_eq_left
#show_template mul_div
#instantiate mul_div with #[Nat, Dvd.dvd, HDiv.hDiv, HMul.hMul]

#check Nat.lcm_dvd_lcm_mul_left_right
template X1 := Nat.lcm_dvd_lcm_mul_left_right
#show_template X1
#instantiate X1 with #[Nat, Nat.lcm, HMul.hMul, Dvd.dvd]

-- id become H1 here... Maybe it chould be c1?
#check Function.comp_id
template comp_id := Function.comp_id
#show_template comp_id
#instantiate comp_id with #[_, _, id, Function.comp]


#check not_false_iff
#check not_true
template exclusive := not_false_iff
#show_template exclusive
#instantiate exclusive with #[True, False]
#instantiate exclusive with #[False, True]

template X0 := iff_iff_eq
-- #instantiate X0 with #[_, _]

#check Nat.div_lt_iff_lt_mul
template X2 := Nat.div_lt_iff_lt_mul
#show_template X2
#instantiate X2 with #[Nat, 0, LT.lt, HDiv.hDiv, HMul.hMul]

#check Fin.mk
#check Fin.exists_iff
template fin_exist := Fin.exists_iff
#show_template fin_exist
#instantiate fin_exist with #[Nat, Fin, _, LT.lt, Fin.mk]
-- Binder issue
-- Idi modda gudisipoina example!!

#check Rat.mkRat_eq_div
template X4 := Rat.mkRat_eq_div
#show_template X4
#instantiate X4 with #[Int, Nat, Rat, mkRat, Int.cast, Nat.cast, HDiv.hDiv]

#check List.all_reverse
template list_rev := List.all_reverse
#show_template list_rev
#instantiate list_rev with #[_, List, Bool, List.reverse, List.all]

#check Array.getElem?_append_left
template array_get := Array.getElem?_append_left
#show_template array_get
#instantiate array_get with #[Nat, _, Array, Option, Array.size, LT.lt, HAppend.hAppend, getElem?]

#check Nat.mul_right_cancel
template cancel := Nat.mul_right_cancel
#show_template cancel



def main : IO Unit := pure ()
