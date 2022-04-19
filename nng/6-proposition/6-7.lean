lemma imp_trans (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)) :=

begin
  intro hpq,
  intro hqr,
  intro hp,
  apply hqr,
  apply hpq,
  exact hp,
end