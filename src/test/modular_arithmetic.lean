import data.nat.basic
import algebra.ring
import tactic

namespace modular
-----------------------------------------------------------------------------------------------
lemma nat.mod_mul_mod (a b n : ℕ) : a * b % n = a % n * b % n :=
begin
  conv_lhs {
    rw [←nat.mod_add_div a n, right_distrib,
        mul_assoc, nat.add_mul_mod_self_left]}
end
-----------------------------------------------------------------------------------------------

variables {n : nat} {npos : fact (n > 1)}
include n npos 

def add' : {k : ℕ // k < n} → {k : ℕ // k < n} → {k : ℕ // k < n} :=
λ a b, match (a,b) with
    | ⟨⟨a₁, ha⟩, ⟨b₁, hb⟩ ⟩ := 
      ⟨ 
        (a₁ + b₁) % n, 
        begin
          apply nat.mod_lt,
          exact nat.lt_of_succ_lt npos,
        end 
      ⟩
    end

@[simp]
lemma add_def': ∀ a {ha} b {hb}, ↑(@add' n npos ⟨a, ha⟩ ⟨b, hb⟩) = (a + b) % n :=
begin
  intros a ha b hb,
  refl,
end

@[simp]
lemma add_def'' : ∀ a b, ↑(@add' n npos a b) = (a.1 + b.1) % n :=
begin
  rintros ⟨a, ha⟩ ⟨b, hb⟩,
  refl,
end

-----------------------------------------------------------------------------------------------
def neg' : {k : ℕ // k < n} → {k : ℕ // k < n} :=
 λ a, match a with 
    | ⟨0, hk⟩ := ⟨0, hk⟩
    | ⟨k + 1, hk⟩ := ⟨n - k - 1, 
      begin 
        show n - (k + 1) < n,
        apply (nat.sub_lt_left_iff_lt_add (by {exact le_of_lt hk} : (k+ 1) ≤ n)).2,
        simp only [nat.succ_pos', lt_add_iff_pos_left],
      end⟩
      end

@[simp]
lemma neg_prop : ∀ a ha, (@neg' n npos ⟨a,ha⟩).1 % n = (n - a) % n :=
begin
  intros,
  simp,
  induction a,
  {
    have h : neg' ⟨0, ha⟩ = ⟨0, ha⟩, by refl,
    rw h,
    simp,
  },
  {
    have h : ↑ (neg' ⟨a_n + 1, ha⟩ ) = n - a_n - 1, by {simp,refl},
    rw h,
    refl,
  }
end 

@[simp]
lemma neg_val : ∀ h, (@neg' n npos ⟨0, h⟩).val = 0 := 
begin 
  intro h,
  refl,
end

@[simp]
lemma neg_val' : ∀ a h, (@neg' n npos ⟨a + 1, h⟩).val = n - a - 1 := 
begin 
  intros a h,
  refl,
end

-----------------------------------------------------------------------------------------------
def mul' : {k : ℕ // k < n} → {k : ℕ // k < n} → {k : ℕ // k < n} :=
λ a b, match (a,b) with 
  | ⟨⟨a₁, ha⟩, ⟨b₁, hb⟩ ⟩ := 
    ⟨ 
      (a₁ * b₁) % n,
      begin 
        apply nat.mod_lt,
        exact nat.lt_of_succ_lt npos,
      end
    ⟩
  end

@[simp]
lemma mul_def : ∀ a {ha} b {hb}, ↑(@mul' n npos ⟨a, ha⟩ ⟨b, hb⟩) = (a * b) % n := 
begin 
  intros,
  refl,
end

@[simp]
lemma mul_def' : ∀ a b, ↑(@mul' n npos a b) = (a.1 * b.1) % n :=
begin 
  rintros ⟨a, ha⟩ ⟨b, hb⟩,
  refl,
end

-----------------------------------------------------------
def zmod (n) (npos : fact (n > 1)) : Type := {k : ℕ // k < n}


def instN {N : ℕ} : fintype ({k : ℕ // k < N}) :=
begin
  --tactic.unfreeze_local_instances,
  induction N with m hm,
  {
    split,
    {
      intro x,
      cases x with x1 h1,
      have : x1 < 0 = false,
      {
        simp,
      },
      rw this at h1,
      contradiction,
    },
    {use ∅},
  },
  {
    set m' : {k : ℕ // k < m.succ} := ⟨m, (by {exact lt_add_one m})⟩ with Hm,
    split,
    swap,
    {      
      have h : {k : ℕ // k < m} ↪ {k : ℕ // k < m.succ},
      {
        split, swap,
        {
          intros x,
          use x,
          cases x,
          exact nat.lt.step x_property,
        },
        intros a1 a2 ha,
        refine subtype.eq _,
        simp at ha,
        assumption,
      },
      set s_coe : finset {k : ℕ // k < m.succ} := finset.map h hm.1,
      use (insert m' s_coe),
    },
    intros x,
    simp,
    by_cases h : x = m',
    {
      left,
      assumption
    },
    {
      right,
      cases x,
      cases hm,
      use x_val,
      simp only [and_true, eq_self_iff_true],
      by_cases H : x_val < m,
      {
        use H,
        apply hm_complete,
      },
      {
        push_neg at H,
        rw Hm at h,
        simp at h,
        obtain h1 := nat.eq_or_lt_of_le H, 
        obtain h2 := nat.lt_add_one_iff.1 x_property,
        induction H' : h1,
        {
          by_contra h0, 
          exact h h_1.symm,
        },
        by_contra,
        have h' : m < m,
        calc m < x_val : h_1
          ... ≤ m : h2,
        exact nat.lt_asymm h' h',
      },
    },
  },
end 

instance {h : fintype ({k : ℕ // k < n})} : fintype (zmod n npos) := 
{ elems := 
    begin
      unfold zmod, 
      exact h.1,
    end ,
  complete := 
    begin
      obtain H := h.2,
      exact H,      
    end
}

-----------------------------------------------------------------------------------------------
instance modN : comm_ring (zmod n npos) :=
{ add := @add' n npos,
  add_assoc := 
    begin 
      rintros ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩,
      ext,
      simp,
      ring,
    end,
  zero := ⟨0, by {exact nat.lt_of_succ_lt npos}⟩,
  zero_add := 
    begin 
      rintro ⟨a, ha⟩,
      ext,
      unfold has_add.add,
      simp only [add_def'', fin.coe_mk],
      rw zero_add a,
      exact nat.mod_eq_of_lt ha,
    end,
  add_zero := 
    begin 
      rintro ⟨a, ha⟩,
      ext,
      unfold has_add.add,
      simp only [add_def'', fin.coe_mk],
      exact nat.mod_eq_of_lt ha,
    end,
  neg := @neg' n npos,
  --sub := _,
  --sub_eq_add_neg := _,
  add_left_neg :=  
    begin 
      rintro ⟨ a, ha⟩ ,
      ext,
      unfold has_neg.neg,
      unfold has_add.add,
      simp,
      set na := @neg' n npos ⟨a,ha⟩ with hna,
      refine (@add_def'' n npos na ⟨a,ha⟩).trans _,
      rw hna,
      induction a,
      {simp, refl,},
      {
        simp,
        have h : a_n.succ = a_n + 1 , by refl,
        rw h at *,
        have h1 : n - (a_n + 1) + (a_n + 1) = n,
        {
          refine (nat.sub_add_eq_max n (a_n + 1)).trans _,
          apply max_eq_left,
          exact le_of_lt ha,
        },
        have h2 : n - a_n - 1 + (a_n + 1) = n - (a_n + 1) + (a_n + 1),
        {
          simp,
          exact nat.sub_sub n a_n 1,
        },
        rw [h2,h1],
        simp,
        refl,
      }
    end,
  add_comm := 
    begin 
      rintros ⟨a,ha⟩ ⟨b,hb⟩,
      ext,
      change ↑(@add' n npos ⟨a,ha⟩ ⟨b,hb⟩) = ↑(@add' n npos ⟨b,hb⟩ ⟨a,ha⟩),
      simp,
      rw add_comm,
    end,
  mul := @mul' n npos,
  mul_assoc := 
    begin 
      rintros ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩,
      ext,
      simp,
      rw <- nat.mod_mul_mod (a*b) c,
      conv_rhs {congr, rw mul_comm},
      rw <- nat.mod_mul_mod (b * c) a,
      conv_rhs {congr, rw [mul_comm, <-mul_assoc]},
    end,
  one := ⟨1, by {assumption}⟩,
  one_mul := 
    begin
      rintro ⟨a, ha⟩,
      change mul' ⟨1, npos⟩ ⟨a, ha⟩ = ⟨a, ha⟩,
      ext,
      rw [mul_def', one_mul],
      dsimp,
      exact nat.mod_eq_of_lt ha,
    end,
  mul_one :=
    begin
      rintro ⟨a, ha⟩,
      change mul' ⟨a, ha⟩ ⟨1, npos⟩ = ⟨a, ha⟩,
      ext,
      rw [mul_def', mul_one],
      dsimp,
      exact nat.mod_eq_of_lt ha,
    end,
  left_distrib := 
    begin
      rintros ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩,
      ext,
      simp only [mul_def', fin.val_eq_coe, add_def'', nat.add_mod_mod, nat.mod_add_mod],
      conv_lhs {congr, rw mul_comm},
      rw <-nat.mod_mul_mod,
      conv_lhs {congr, rw [mul_comm, nat.left_distrib]},
    end,
  right_distrib :=
    begin
      rintros ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩,
      ext,
      simp only [mul_def', fin.val_eq_coe, add_def'', nat.add_mod_mod, nat.mod_add_mod],
      show (a + b) % n * c % n = (a * c + b * c) % n,
      rw <-nat.mod_mul_mod,
      conv_lhs {congr, rw nat.right_distrib},
    end,
  mul_comm := 
    begin
      rintros ⟨a,ha⟩ ⟨b,hb⟩,
      change mul' ⟨a, ha⟩ ⟨b,hb⟩ = mul' ⟨b,hb⟩ ⟨a, ha⟩,
      ext,
      show a * b % n = b * a % n,
      rw nat.mul_comm,
    end 
}

--instance modN : has_pow (zmod n npos) ℕ :=
--{ pow := _ }


def int_to_modN : ℤ →+* (zmod n npos) :=
{ to_fun := λ m, ⟨m % n, by {}⟩,
  map_one' := _,
  map_mul' := _,
  map_zero' := _,
  map_add' := _ }



end modular

#check modular.modN 

open modular 

variable n : ℕ 
variable (fact : n > 1)

variables a : zmod 5 (by {simp,})

def one : zmod 5 (by {simp,}) := 1 
def two : zmod 5 (by {simp,}) := 2

example : one + one = two := by {refl}

theorem sdf : one + one + one + one + one = (0 : zmod 5 _) := by {refl} 

#print instN 


example : ∀ a : zmod 5 (by {simp,}), a*a*a*a*a = a :=
begin 
  --induction a with b prop,
  --set asdf := 
  --obtain := instN 5,
  intro a,
  haveI H : fintype {k : ℕ // k < 5} := @instN 5 (by simp) 5,
  haveI h : fintype (zmod 5 (by {simp,})) := @zmod.fintype _ _ H,
  set A := h.elems with hA,
  set Ac := h.complete with hAc,
  set B := H.elems with hB,
  set Bc := H.complete with hBc,
  obtain H1 := Ac a,
  obtain H2 := Bc a,
  --unfreezingI
  {
    fin_cases *, -- with [0,1,2,3,4],
  },
  assumption,
end 


