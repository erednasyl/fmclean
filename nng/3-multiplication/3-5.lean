lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
begin
  induction c with d hd,
  rw mul_zero,
  rw mul_zero,
  rw mul_zero,
  refl,
  rw mul_succ,
  rw mul_succ,
  rw hd,
  rw mul_add,
  refl,
end