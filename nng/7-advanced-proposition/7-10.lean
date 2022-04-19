lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) :=

begin
  intro h,
  intro p,
  repeat {rw not_iff_imp_false at h},
  by_cases p : P; by_cases q : Q,
  repeat {cc},
end