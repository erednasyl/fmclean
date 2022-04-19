theorem add_right_cancel (a t b : mynat) : a + t = b + t → a = b :=

begin
intro h,
induction t with k hk,
repeat {rw add_zero at h},
exact h,
rw add_succ at h,
rw add_succ at h,
have hpure := succ_inj h,
apply hk,
exact hpure,
end