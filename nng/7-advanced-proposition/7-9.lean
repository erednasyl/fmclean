lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q :=

begin
  intro pp,
  cases pp with pt pf,
  exfalso,
  apply pf,
  exact pt,
end