example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) :=

begin
  intros f h p,
  apply f,
  apply p,
  apply h,
  exact p,
end