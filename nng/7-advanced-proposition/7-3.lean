lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R :=

begin
  intros h k,
  cases k with q r,
  cases h with p q,
  split,
  exact p,
  exact r,
end