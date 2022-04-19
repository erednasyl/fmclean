import mynat.add -- + on mynat
import mynat.mul -- * on mynat

example : mynat → mynat :=
begin
  intro n,
  exact 3*n+2,
end