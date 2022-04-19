lemma one_mul (m : mynat) : 1 * m = m :=
begin
  induction m with d hd,
  rw mul_zero,
  refl,
  rw one_eq_succ_zero,
  rw mul_succ,
  rw succ_eq_add_one,
  rw zero_add,
  rw hd,
  refl,
end
