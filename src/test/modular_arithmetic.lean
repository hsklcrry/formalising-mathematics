import data.nat.basic
import tactic

namespace modular

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

--@[simp]
instance : has_add {k : ℕ // k < n} :=
{ add := @add' n npos }

--lemma add_def : ∀ (a b : {k : ℕ // k < n}), a + b = @add' n npos a b := 

def modN [npos : n > 1] : comm_ring {k : ℕ // k < n} :=
{ add := @add' n npos,
  add_assoc := 
    begin 
      rintros ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩,
      ext,
      simp,
      ring,
    end,
  zero := ⟨0, by {linarith}⟩,
  zero_add := 
    begin 
      rintro ⟨a, ha⟩,
      ext,
      unfold has_add.add,
      simp,
      exact nat.mod_eq_of_lt ha,
    end,
  add_zero := 
    begin 
      rintro ⟨a, ha⟩,
      ext,
      unfold has_add.add,
      simp,
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
  mul := _,
  mul_assoc := _,
  one := _,
  one_mul := _,
  mul_one := _,
  left_distrib := _,
  right_distrib := _,
  mul_comm := _ }


