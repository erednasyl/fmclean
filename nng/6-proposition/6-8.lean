lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=

begin
  rw not_iff_imp_false,
  rw not_iff_imp_false,
  intro h,
  intro q,
  intro m,
  apply q,
  apply h,
  exact m,
end