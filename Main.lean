import LeanLemmanaid

set_option pp.proofs true

/-
## Sanity Check
Testing examples that don't need Mathlib
-/
-- #check Nat.add_comm
template comm := Nat.add_comm

/--
info: T1 : Type
x1 x2 : T1
H1 : T1 → T1 → T1
⊢ H1 x1 x2 = H1 x2 x1
-/
#guard_msgs in
#show_template comm
template comm' := H1 x1 x2 = H1 x2 x1 where
  T1 : Type, x1 : T1, x2 : T1, H1 : T1 → T1 → T1
/--
info: T1 : Type
x1 x2 : T1
H1 : T1 → T1 → T1
⊢ H1 x1 x2 = H1 x2 x1
-/
#guard_msgs in
#show_template comm'
/-- info: ∀ (x1 x2 : Nat), x1 + x2 = x2 + x1 -/
#guard_msgs in
#instantiate comm with #[Nat, HAdd.hAdd]

-- #check Nat.add_add_add_comm
template super_comm := Nat.add_add_add_comm
/--
info: T1 : Type
x1 x2 x3 x4 : T1
H1 : T1 → T1 → T1
⊢ H1 (H1 x1 x2) (H1 x3 x4) = H1 (H1 x1 x3) (H1 x2 x4)
-/
#guard_msgs in
#show_template super_comm
-- #inst_temp H1 (H1 x1 x2) (H1 x3 x4) = H1 (H1 x1 x3) (H1 x2 x4) with
  -- #[Nat, HAdd.hAdd]

-- #check Nat.add_assoc
template assoc := Nat.add_assoc
/--
info: T1 : Type
x1 x2 x3 : T1
H1 : T1 → T1 → T1
⊢ H1 (H1 x1 x2) x3 = H1 x1 (H1 x2 x3)
-/
#guard_msgs in
#show_template assoc
/-- info: ∀ (x1 x2 x3 : Nat), x1 + x2 + x3 = x1 + (x2 + x3) -/
#guard_msgs in
#instantiate assoc with #[Nat, HAdd.hAdd]

-- #check Nat.add_zero
-- #check Fin.add_zero
variable (n : Nat)
template right_id := Nat.add_zero
/--
info: T1 : Type
x1 c1 : T1
H1 : T1 → T1 → T1
⊢ H1 x1 c1 = x1
-/
#guard_msgs in
#show_template right_id
/-- info: ∀ (x1 : Nat), x1 + 0 = x1 -/
#guard_msgs in
#instantiate right_id with #[Nat, 0, HAdd.hAdd]
/-- info: ∀ (x_0 : Nat) (x1 : Fin (x_0 + 1)), x1 + 0 = x1 -/
#guard_msgs in
#instantiate right_id with #[Fin (_+1), 0, HAdd.hAdd]
/-- info: ∀ (x_0 : Nat) (x1 c1 : Fin x_0), x1 + c1 = x1 -/
#guard_msgs in
#instantiate right_id with #[Fin _, _, HAdd.hAdd]


-- #check Int.neg_add
template neg_distrib := Int.neg_add
/--
info: T1 : Type
x1 x2 : T1
H1 : T1 → T1 → T1
H2 : T1 → T1
⊢ H2 (H1 x1 x2) = H1 (H2 x1) (H2 x2)
-/
#guard_msgs in
#show_template neg_distrib
/-- info: ∀ (x1 x2 : Int), -(x1 + x2) = -x1 + -x2 -/
#guard_msgs in
#instantiate neg_distrib with #[Int, HAdd.hAdd, Neg.neg]

-- #check Vector.add_comm
template depdt_comm := Vector.add_comm
/--
info: T1 : Sort u_1
T3 : Type
T2 : Sort u_2 → T3 → Sort u_3
x4 : T3
H1 : T1 → T1 → T1
H2 : T2 T1 x4 → T2 T1 x4 → T2 T1 x4
⊢ (∀ (x1 x2 : T1), H1 x1 x2 = H1 x2 x1) → ∀ (x3 x5 : T2 T1 x4), H2 x3 x5 = H2 x5 x3
-/
#guard_msgs in
#show_template depdt_comm
/--
info: ∀ (x4 : Nat), (∀ (x1 x2 : Int), x1 + x2 = x2 + x1) → ∀ (x3 x5 : Vector Int x4), x3 + x5 = x5 + x3
-/
#guard_msgs in
#instantiate depdt_comm with #[Int, Nat, Vector, HAdd.hAdd, HAdd.hAdd]

-- #check Nat.add_mul
template right_distrib := Nat.add_mul
/--
info: T1 : Type
x1 x2 x3 : T1
H1 H2 : T1 → T1 → T1
⊢ H2 (H1 x1 x2) x3 = H1 (H2 x1 x3) (H2 x2 x3)
-/
#guard_msgs in
#show_template right_distrib
/-- info: ∀ (x1 x2 x3 : Nat), (x1 + x2) * x3 = x1 * x3 + x2 * x3 -/
#guard_msgs in
#instantiate right_distrib with #[Nat, HAdd.hAdd, HMul.hMul]

-- #check Nat.add_div
template div_right_distrib := Nat.add_div
/--
info: T1 : Type
x1 x2 x3 c1 c2 : T1
H1 : T1 → T1 → Prop
H2 H3 H4 : T1 → T1 → T1
H5 : T1 → T1 → Prop
H6 : Prop → T1 → T1 → T1
⊢ H1 c1 x1 → H3 (H2 x2 x3) x1 = H2 (H2 (H3 x2 x1) (H3 x3 x1)) (H6 (H5 x1 (H2 (H4 x2 x1) (H4 x3 x1))) c2 c1)
-/
#guard_msgs in
#show_template div_right_distrib
/--
info: ∀ (x1 x2 x3 : Nat), 0 < x1 → (x2 + x3) / x1 = x2 / x1 + x3 / x1 + if x1 ≤ x2 % x1 + x3 % x1 then 1 else 0
-/
#guard_msgs in
#instantiate div_right_distrib with #[Nat, 0, 1, LT.lt, HAdd.hAdd, HDiv.hDiv, HMod.hMod, LE.le, ite]

-- #check Nat.div_add_mod
template div_law := Nat.div_add_mod
/--
info: T1 : Type
x1 x2 : T1
H1 H2 H3 H4 : T1 → T1 → T1
⊢ H4 (H2 x2 (H1 x1 x2)) (H3 x1 x2) = x1
-/
#guard_msgs in
#show_template div_law
/-- info: ∀ (x1 x2 : Nat), x2 % (x1 / x2) * (x1 + x2) = x1 -/
#guard_msgs in
#instantiate div_law with #[Nat, HDiv.hDiv, HMod.hMod, HAdd.hAdd, HMul.hMul]

-- #check Nat.eq_mul_of_div_eq_left
template mul_div := Nat.eq_mul_of_div_eq_left
/--
info: T1 : Type
x1 x2 x3 : T1
H1 : T1 → T1 → Prop
H2 H3 : T1 → T1 → T1
⊢ H1 x1 x2 → H2 x2 x1 = x3 → x2 = H3 x3 x1
-/
#guard_msgs in
#show_template mul_div
/-- info: ∀ (x1 x2 x3 : Nat), x1 ∣ x2 → x2 / x1 = x3 → x2 = x3 * x1 -/
#guard_msgs in
#instantiate mul_div with #[Nat, Dvd.dvd, HDiv.hDiv, HMul.hMul]

-- #check Nat.lcm_dvd_lcm_mul_left_right
template X1 := Nat.lcm_dvd_lcm_mul_left_right
/--
info: T1 : Type
x1 x2 x3 : T1
H1 H2 : T1 → T1 → T1
H3 : T1 → T1 → Prop
⊢ H3 (H1 x1 x2) (H1 x1 (H2 x3 x2))
-/
#guard_msgs in
#show_template X1
/-- info: ∀ (x1 x2 x3 : Nat), x1.lcm x2 ∣ x1.lcm (x3 * x2) -/
#guard_msgs in
#instantiate X1 with #[Nat, Nat.lcm, HMul.hMul, Dvd.dvd]

-- id become H1 here... Maybe it chould be c1?
-- #check Function.comp_id
template comp_id := Function.comp_id
/--
info: T1 : Sort u_1
T2 : Sort u_2
x1 : T1 → T2
H1 : T1 → T1
H2 : (T1 → T2) → (T1 → T1) → T1 → T2
⊢ H2 x1 H1 = x1
-/
#guard_msgs in
#show_template comp_id
/-- info: ∀ {T1 : Sort u_1} {T2 : Sort u_2} (x1 : T1 → T2), x1 ∘ id = x1 -/
#guard_msgs in
#instantiate comp_id with #[_, _, id, Function.comp]


-- #check not_false_iff
-- #check not_true
template exclusive := not_false_iff
/--
info: H1 H2 : Prop
⊢ ¬H1 ↔ H2
-/
#guard_msgs in
#show_template exclusive
/-- info: ¬True ↔ False -/
#guard_msgs in
#instantiate exclusive with #[True, False]
/-- info: ¬False ↔ True -/
#guard_msgs in
#instantiate exclusive with #[False, True]

template X0 := iff_iff_eq
/-- info: ∀ (H1 H2 : Prop), (H1 ↔ H2) ↔ H1 = H2 -/
#guard_msgs in--
#instantiate X0 with #[_, _]

-- #check Nat.div_lt_iff_lt_mul
template X2 := Nat.div_lt_iff_lt_mul
/--
info: T1 : Type
x1 x2 x3 c1 : T1
H1 : T1 → T1 → Prop
H2 H3 : T1 → T1 → T1
⊢ H1 c1 x1 → (H1 (H2 x2 x1) x3 ↔ H1 x2 (H3 x3 x1))
-/
#guard_msgs in
#show_template X2
/-- info: ∀ (x1 x2 x3 : Nat), 0 < x1 → (x2 / x1 < x3 ↔ x2 < x3 * x1) -/
#guard_msgs in
#instantiate X2 with #[Nat, 0, LT.lt, HDiv.hDiv, HMul.hMul]

-- #check Fin.mk
-- #check Fin.exists_iff
template fin_exist := Fin.exists_iff
/--
info: T2 : Type
T1 : T2 → Type
x2 : T2
H1 : T1 x2 → Prop
H2 : T2 → T2 → Prop
H3 : (x5 : T2) → H2 x5 x2 → T1 x2
⊢ (∃ x1, H1 x1) ↔ ∃ x3 x4, H1 (H3 x3 x4)
-/
#guard_msgs in
#show_template fin_exist
/-- info: ∀ (x2 : Nat) (H1 : Fin x2 → Prop), (∃ x1, H1 x1) ↔ ∃ x3 x4, H1 ⟨x3, x4⟩ -/
#guard_msgs in
#instantiate fin_exist with #[Nat, Fin, _, LT.lt, Fin.mk]
-- Binder issue
-- Idi modda gudisipoina example!!

-- #check Rat.mkRat_eq_div
template X4 := Rat.mkRat_eq_div
/--
info: T1 T2 T3 : Type
x1 : T1
x2 : T2
H1 : T1 → T2 → T3
H2 : T1 → T3
H3 : T2 → T3
H4 : T3 → T3 → T3
⊢ H1 x1 x2 = H4 (H2 x1) (H3 x2)
-/
#guard_msgs in
#show_template X4
/-- info: ∀ (x1 : Int) (x2 : Nat), mkRat x1 x2 = ↑x1 / ↑x2 -/
#guard_msgs in
#instantiate X4 with #[Int, Nat, Rat, mkRat, Int.cast, Nat.cast, HDiv.hDiv]

-- #check List.all_reverse
template list_rev := List.all_reverse
/--
info: T1 : Sort u_1
T2 : Sort u_2 → Sort u_3
T3 : Type
x1 : T2 T1
x2 : T1 → T3
H1 : T2 T1 → T2 T1
H2 : T2 T1 → (T1 → T3) → T3
⊢ H2 (H1 x1) x2 = H2 x1 x2
-/
#guard_msgs in
#show_template list_rev
/--
info: ∀ {T1 : Type u_1} (x1 : List T1) (x2 : T1 → Bool) (H1 : List T1 → List T1) (H2 : List T1 → (T1 → Bool) → Bool),
  H2 (H1 x1) x2 = H2 x1 x2
-/
#guard_msgs in
#instantiate list_rev with #[_, List, Bool, _, _]
/-- info: ∀ {T1 : Type u_1} (x1 : List T1) (x2 : T1 → Bool), x1.reverse.all x2 = x1.all x2 -/
#guard_msgs in
#instantiate list_rev with #[_, List, Bool, List.reverse, List.all]

-- #check Array.getElem?_append_left
template array_get := Array.getElem?_append_left
/--
info: T1 : Type
T2 : Sort u_1
T3 : Sort u_2 → Sort u_3
T4 : Sort u_4 → Sort u_5
x1 : T1
x2 x3 : T3 T2
H1 : T3 T2 → T1
H2 : T1 → T1 → Prop
H3 : T3 T2 → T3 T2 → T3 T2
H4 : T3 T2 → T1 → T4 T2
⊢ H2 x1 (H1 x2) → H4 (H3 x2 x3) x1 = H4 x2 x1
-/
#guard_msgs in
#show_template array_get
/--
info: ∀ {T2 : Type u_1} (x1 : Nat) (x2 x3 : Array T2), x1 < x2.size → (x2 ++ x3)[x1]? = x2[x1]?
-/
#guard_msgs in
#instantiate array_get with #[Nat, _, Array, Option, Array.size, LT.lt, HAppend.hAppend, getElem?]

-- #check Nat.mul_right_cancel
template cancel := Nat.mul_right_cancel
/--
info: T1 : Type
x1 x2 x3 c1 : T1
H1 : T1 → T1 → Prop
H2 : T1 → T1 → T1
⊢ H1 c1 x1 → H2 x2 x1 = H2 x3 x1 → x2 = x3
-/
#guard_msgs in
#show_template cancel
/-- info: ∀ (x1 x2 x3 : Nat), 0 < x1 → x2 * x1 = x3 * x1 → x2 = x3 -/
#guard_msgs in
#instantiate cancel with #[Nat, 0, LT.lt, HMul.hMul]

-- #check congrFun
template congr_temp := congrFun
/--
info: T1 : Sort u_1
T2 : T1 → Sort u_2
H1 H2 : (x3 : T1) → T2 x3
⊢ H1 = H2 → ∀ (x1 : T1), H1 x1 = H2 x1
-/
#guard_msgs in
#show_template congr_temp
/--
info: ∀ {T1 : Sort u_1} {T2 : T1 → Sort u_2} (H1 H2 : (x3 : T1) → T2 x3), H1 = H2 → ∀ (x1 : T1), H1 x1 = H2 x1
-/
#guard_msgs in
#instantiate congr_temp with #[_, _, _, _]

-- #check Function.rightInverse_of_injective_of_leftInverse
template X5 := Function.rightInverse_of_injective_of_leftInverse
/--
info: T1 : Sort u_1
T2 : Sort u_2
x1 : T1 → T2
x2 : T2 → T1
H1 : (T1 → T2) → Prop
H2 H3 : (T1 → T2) → (T2 → T1) → Prop
⊢ H1 x1 → H2 x1 x2 → H3 x1 x2
-/
#guard_msgs in
#show_template X5
/--
info: ∀ {T1 : Sort u_1} {T2 : Sort u_2} (x1 : T1 → T2) (x2 : T2 → T1),
  Function.Injective x1 → Function.LeftInverse x1 x2 → Function.RightInverse x1 x2
-/
#guard_msgs in
#instantiate X5 with #[_, _, Function.Injective, Function.LeftInverse, Function.RightInverse]


def main : IO Unit := pure ()
