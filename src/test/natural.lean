import data.nat.basic
import tactic

#check nat

#print instances has_dvd
#check nat.has_dvd 

example : ∀ n : nat, n > 0 → n / n * n = n :=
begin
  intros n h,
  rw mul_comm,
  rw nat.div_self h,
  simp,
end


