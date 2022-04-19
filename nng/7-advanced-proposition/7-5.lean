lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=

begin
  intro h,
  cases h with hpq hqp,
  intro m,
  cases m with hqr hrq,
  split,
  intro i,
  apply hqr,
  apply hpq,
  exact i,
  intro i,
  apply hqp,
  apply hrq,
  exact i,
end