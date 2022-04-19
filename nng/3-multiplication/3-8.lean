lemma mul_comm (a b : mynat) : a * b = b * a :=
begin
  induction b with d hd,
  rw mul_zero,
  rw zero_mul,
  refl,
  rw mul_succ,
  rw succ_mul,
  rw hd,
  refl,
end
