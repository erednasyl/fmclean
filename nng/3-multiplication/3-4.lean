lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b :=
begin
  induction a with k hk,
  rw zero_add,
  rw mul_zero,
  rw zero_add,
  refl,
  rw succ_add,
  rw mul_succ,
  rw hk,
  rw mul_succ,
  rw add_right_comm,
  refl,
end
