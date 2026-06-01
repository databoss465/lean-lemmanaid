import LeanLemmanaid

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

-- Sanity Checks
#check Nat.add_comm
#test_abs Nat.add_comm
#inst_temp H1 x1 x2 = H1 x2 x1 with
 #[Nat, _, HAdd.hAdd]

#check Nat.add_add_add_comm
#test_abs Nat.add_add_add_comm
#inst_temp H1 (H1 x1 x2) (H1 x3 x4) = H1 (H1 x1 x3) (H1 x2 x4) with
  #[Nat, HAdd.hAdd]

#check Nat.add_assoc
#test_abs Nat.add_assoc
#inst_temp H1 (H1 x1 x2) x3 = H1 x1 (H1 x2 x3) with
  #[Nat, _, HAdd.hAdd]

#check Nat.add_zero
#test_abs Nat.add_zero
#inst_temp H1 x1 c1 = x1 with
  #[Nat, _, 0, HAdd.hAdd]
