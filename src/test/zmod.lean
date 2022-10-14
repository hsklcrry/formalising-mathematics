import data.zmod.basic
import data.zmod.parity
import tactic

variables a : zmod 5

example : a*a*a*a*a = a := 
begin 
  change fin 5 at a,
  fin_cases a; refl,
end

variables (n : ℕ) (x : zmod n)

example : (∃ b, b*x = 1) → x^n = x :=
begin 
  intro h,
  cases h with b hb,

end
