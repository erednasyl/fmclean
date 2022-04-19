lemma or_symm (P Q : Prop) : P ∨ Q → Q ∨ P :=

begin
  intro pq,
  cases pq,
  right,
  exact pq,
  left,
  exact pq,
end