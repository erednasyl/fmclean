lemma add_right_eq_zero {a b : mynat} : a + b = 0 → a = 0 :=

begin
cases b with d,
intro a,
rw add_zero at a,
exact a,
intro had,
exfalso,
rw add_succ at had,
have hs := succ_ne_zero (a + d),
have hf := hs(had),
exact hf,
end