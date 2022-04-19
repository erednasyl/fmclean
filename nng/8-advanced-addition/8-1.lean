theorem succ_inj' {a b : mynat} (hs : succ(a) = succ(b)) :  a = b := 

begin
apply succ_inj,
exact hs,
end