split,
apply eq_zero_or_eq_zero_of_mul_eq_zero,
intro ab,
cases b,
rw mul_zero,
refl,
cases ab with a b,
rw a,
rw zero_mul,
refl,
rw b,
rw mul_zero,
refl,