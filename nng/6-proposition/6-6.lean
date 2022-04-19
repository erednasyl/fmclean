example (P Q R : Prop) : (P → (Q → R)) → ((P → Q) → (P → R)) :=

begin
  intros m n o,
  apply m,
  apply o,
  apply n,
  exact o,
end