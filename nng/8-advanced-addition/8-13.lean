lemma ne_succ_self (n : mynat) : n ≠ succ n :=

begin
  induction n with i hi,
  apply zero_ne_succ,
  intro,
  rw succ_eq_succ_iff at a,
  have hs := hi a,
  exact hs,
end