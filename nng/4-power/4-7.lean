induction n with k hk,
rw pow_zero,
rw mul_zero,
refl,
rw pow_succ,
rw hk,
rw mul_succ,
rw pow_add,
refl,