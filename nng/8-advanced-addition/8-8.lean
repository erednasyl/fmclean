lemma eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a → b = 0 :=

begin
intro aba,
induction a with k hk,
rw zero_add at aba,
exact aba,
rw succ_add at aba,
rw hk,
refl,
have hf := succ_inj aba,
exact hf,
end