lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t :=
begin
    induction t with w hw,
    repeat {rw mul_zero},
    refl,
    repeat {rw mul_succ},
    rw hw,
    simp,
end
