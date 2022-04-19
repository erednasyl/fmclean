lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=
begin
  induction c with k hk,
  rw add_zero,
  rw add_zero,
  refl,
  rw add_succ,
  rw hk,
  rw add_succ,
  rw succ_add,
  refl,
end