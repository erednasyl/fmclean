lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) :=
begin
  induction c with d hd,
  repeat {rw mul_zero},
  rw mul_succ,
  rw mul_add,
  rw hd,
  rw mul_succ,
  rw mul_add,
  simp,
  rw mul_comm,
  refl,
end