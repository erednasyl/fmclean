lemma add_left_eq_zero {{a b : mynat}} (H : a + b = 0) : b = 0 :=

begin
cases b with d,
refl,
exfalso,
rw add_succ at H,
have hs := succ_ne_zero (a+d),
have hf := hs(H),
exact hf,
end