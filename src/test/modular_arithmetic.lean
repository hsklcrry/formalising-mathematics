import data.nat.basic
import tactic

namespace modular

variables {n : nat} [npos : n > 1]

def add' {n} {npos : n > 1} : {k : ℕ // k < n} → {k : ℕ // k < n} → {k : ℕ // k < n} :=
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

--localized "infixl ` + `:75 := add'" in modular

#reduce (⟨3, by {linarith,}⟩ : {k : ℕ // k < 5}) + (⟨3, by {linarith,}⟩ : {k : ℕ // k < 5})

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

lemma mono_coe : ∀ (a b : nat), a ≤ b ↔ (a : ℤ) ≤ b :=
begin 
  intros a b,
  split,
  {
    intro h,
    linarith,
  },
  {
    intro h,
    linarith,
  }
end 

def modN [npos : n > 1] : comm_ring {k : ℕ // k < n} :=
{ add := @add' n npos,
  add_assoc := 
    begin 
      rintros ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩,
      ext,
      simp,
      ring,
    end,
  zero := ⟨0, by exact nat.lt_of_succ_lt npos⟩,
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
  neg := λ a, match a with 
    | ⟨0, hk⟩ := ⟨0, hk⟩
    | ⟨k + 1, hk⟩ := ⟨n - k - 1, 
      begin 
        --induction k,
        have H1 : (n : ℤ) - k - 1 < (n : ℤ),
        {
          linarith,
        },
        have H2 : 0 < (n : ℤ) - k - 1,
        {
          linarith,
        },
        by_contra,
        push_neg at h,
        have : n + k + 1 ≤ n,
        {
          obtain H' := nat.add_le_add_right h (k + 1),
          conv_rhs at H' {},
          simp at H5,
        }
        have H3 : (n : ℤ) ≤ n - k - 1,
        {
          rw mono_coe at h,
          apply h,
        },
        have : ↑n < ↑n,
        {
          calc ↑n ≤ ↑n - ↑k - 1 : by {linarith}
          ... < ↑n : by {refine H1},
        },
        have H : n < n + k + 1,
        {calc n ≤ n + k : by {exact nat.le.intro rfl}
          ... < n + k + 1 : by {exact lt_add_one (n + k)}},
        have H1 : n - k > 1,
        {sorry,},
        rw nat.sub_sub,
        rw lt_iff_le_not_le at hk,
        rw <-nat.lt_succ_of_le at hk,
        apply sub_le_sub_right_iff,
        calc n - k - 1 < n - k : by {}
          ... = n : by {library_search},
      end⟩
      end,
  sub := _,
  sub_eq_add_neg := _,
  add_left_neg := _,
  add_comm := _,
  mul := _,
  mul_assoc := _,
  one := _,
  one_mul := _,
  mul_one := _,
  left_distrib := _,
  right_distrib := _,
  mul_comm := _ }


