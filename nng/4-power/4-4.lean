lemma one_pow (m : mynat) : (1 : mynat) ^ m = 1 :=
begin
  induction m with k hk,
  rw pow_zero,
  refl,
  rw pow_succ,
  rw hk,
  rw mul_one,
  refl,
end