theorem add_left_cancel (t a b : mynat) : t + a = t + b → a = b :=

begin
induction t with m hm,
rw zero_add,
rw zero_add,
intro ab,
exact ab,
rw succ_add,
rw succ_add,
intro succma,
have hf := succ_inj succma,
apply hm,
exact hf,
end