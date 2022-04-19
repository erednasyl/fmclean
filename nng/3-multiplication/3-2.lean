lemma mul_one (m : mynat) : m * 1 = m :=
begin
  induction m with d hd,
  rw zero_mul,
  refl,
  rw one_eq_succ_zero,
  rw mul_succ,
  rw mul_zero,
  rw zero_add,
  refl,
end
