import LeanLemmanaid

set_option pp.proofs false

-- Sanity Checks
#check Nat.add_comm
#abstract Nat.add_comm
-- #inst_temp H1 x1 x2 = H1 x2 x1 with
--  #[Nat, _, HAdd.hAdd]

#check Nat.add_add_add_comm
#abstract Nat.add_add_add_comm
-- #inst_temp H1 (H1 x1 x2) (H1 x3 x4) = H1 (H1 x1 x3) (H1 x2 x4) with
  -- #[Nat, HAdd.hAdd]

#check Nat.add_assoc
#abstract Nat.add_assoc
-- #inst_temp H1 (H1 x1 x2) x3 = H1 x1 (H1 x2 x3) with
--   #[Nat, _, HAdd.hAdd]

#check Nat.add_zero
#abstract Nat.add_zero
-- #inst_temp H1 x1 c1 = x1 with
--   #[Nat, _, 0, HAdd.hAdd]

#check Int.neg_add
#abstract Int.neg_add
-- #inst_temp H2 (H1 x1 x2) = H1 (H2 x1) (H2 x2) with #[Int, HAdd.hAdd, Neg.neg]

#check Vector.add_comm
#abstract Vector.add_comm
-- #inst_temp ∀ x1 x2, H1 x1 x2 = H1 x2 x1 → ∀ x3 x4, H2 x3 x4 = H2 x4 x3
  -- with #[Int, Vector Int _, _, _, HAdd.hAdd, HAdd.hAdd]

#check Nat.add_mul
#abstract Nat.add_mul
-- #inst_temp H2(H1 x1 x2)x3 = H1(H2 x1 x3)(H2 x2 x3)
--   with #[Nat, _, HAdd.hAdd, HMul.hMul]

#check Nat.add_div
#abstract Nat.add_div
-- #test_stx H1 c1 x1 → H3(H2 x2 x3)x1 = H2(H2(H3 x2 x1)(H3 x3 x1))(H6(H5 x1(H2(H4 x2 x1)(H4 x3 x1)))c2 c1)
-- Want ite in DSL! Same issue is that type of ite depends on its args!
-- #inst_temp H1 c1 x1 → H3(H2 x2 x3)x1 = H2(H2(H3 x2 x1)(H3 x3 x1))(H6(H5 x1(H2(H4 x2 x1)(H4 x3 x1)))c2 c1)
--   with #[Nat, Nat, Nat, Nat, Nat, 0, 1, LT.lt, HAdd.hAdd, HDiv.hDiv, HMod.hMod, LE.le, @ite Nat]

#check Nat.div_add_mod
#abstract Nat.div_add_mod
-- #inst_temp H4(H2 x2(H1 x1 x2))(H3 x1 x2) = x1
--   with #[Nat, _, _, _, _, HDiv.hDiv, HMul.hMul, HAdd.hAdd, HMod.hMod]

#check Nat.eq_mul_of_div_eq_left
#abstract Nat.eq_mul_of_div_eq_left
-- #inst_temp H1 x1 x2 → H2 x2 x1 = x3 → x2 = H3 x3 x1
--   with #[Nat, _, _, Dvd.dvd, HDiv.hDiv, HMul.hMul]

#check Nat.lcm_dvd_lcm_mul_left_right
#abstract Nat.lcm_dvd_lcm_mul_left_right

-- DEBUG!
#check Function.comp_id
#abstract Function.comp_id
-- #inst_temp H2 x1(H1) = x1
--   with #[_, _, id, Function.comp]

#check not_false_iff
#abstract not_false_iff
-- #inst_temp ¬H1 ↔ H2
--   with #[False, True]

-- #abstract iff_iff_eq
-- #inst_temp (H1 ↔ H2) ↔ H1 = H2
--   with #[_, _]

#check Nat.div_lt_iff_lt_mul
#abstract Nat.div_lt_iff_lt_mul
-- #inst_temp H1 c1 x1 → H1(H2 x2 x1)x3 ↔ H1 x2(H3 x3 x1)
--   with #[Nat, Nat, 0, LT.lt, HMul.hMul, HDiv.hDiv]

#check Fin.mk
#check Fin.exists_iff
#abstract Fin.exists_iff
-- #test_stx ∃ x1, H1 x1 ↔ ∃ x2, ∃ x3, H1(H2 x2 x3)
-- Dependent types issue!
-- #inst_temp ∃ x1, H1 x1 ↔ ∃ x2, ∃ x3, H1(H2 x2 x3)
--   with #[Nat, Nat, _, fun (Fin _) => Prop, Fin.mk]

#check Rat.mkRat_eq_div
#abstract Rat.mkRat_eq_div
-- #inst_temp H1 x1 x2 = H4(H2 x1)(H3 x2)
--   with #[_, _, _, _, _, mkRat, Int.cast, Nat.cast, HDiv.hDiv]
