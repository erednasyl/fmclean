theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b :=

begin
split,
apply add_right_cancel,
intro ab,
rw ab,
refl,
end