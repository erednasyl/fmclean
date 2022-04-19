example (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)) :=

begin
  intro m,
  intro n,
  intro o,
  apply n,
  apply m,
  exact o,
end