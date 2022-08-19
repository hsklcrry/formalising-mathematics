
--import init.logic
import algebra.big_operators.basic
import data.finset.basic
--import init.data.nat.lemmas
import data.nat.basic
import tactic

--open_locale classical 
--noncomputable theory 

#eval 1 % 0 

def is_prime (p : nat) : Prop := 
  p > 1 ∧ ¬ ∃ n, 1 < n ∧ n < p ∧ p % n = 0

theorem one_is_not_prime : ¬ is_prime 1 :=
begin
  rw is_prime,
  intro h,
  cases h with h₁ _,
  linarith,
end 

theorem two_is_prime : is_prime 2 :=
begin
  rw is_prime,
  split,
  {linarith},
  by_contra,
  rcases h with ⟨n, ⟨h₁, h₂, h₃⟩ ⟩ ,
  linarith,
end 

theorem multiples_are_not_prime (p : nat) {h : p > 1} 
  : ∀ k, (k > p ∧ k % p = 0) → ¬ is_prime k :=
begin 
  intro k,
  rintro ⟨h1,h2⟩,
  intro hk,
  rw is_prime at *,
  rcases hk with ⟨kp, hk⟩,
  apply hk,
  use p,
  split,
  {linarith}, 
  split,
  {linarith},
  assumption,
end 

example : ¬is_prime 4 := 
begin 
  apply multiples_are_not_prime 2,
  {by {split,linarith,refl}},
  linarith,
end 

def primes : set ℕ := { p : ℕ | is_prime p}

example : 2 ∈ primes := by exact two_is_prime

open_locale big_operators
 --.prod_eq_mul_prod_diff_singleton

lemma div_div : ∀ n m, m > 1 → ((n % m = 0) ↔ ∃ k, n = k * m) :=
begin 
  intros n m hm,
  split,
  {
    intro hnm,
    use n / m,
    have H : n % m + m * (n / m) = n, from nat.mod_add_div _ _,
    rw hnm at H,
    simp at H,
    apply symm,
    rw mul_comm,
    refine H,
  },
  {
    rintros ⟨k, rfl⟩,
    exact nat.mul_mod_left k m,
  }
end 

lemma lemma_div : ∀ a b c : ℕ , c > 0 → a * b * c / c = a * b :=
begin
    intros a b c hc,
    apply nat.mul_div_left _,
    exact hc,
end

lemma has_prime_div : ∀ n > 1, ∃ q ∈ primes, n = q * (n / q) :=
begin
    intros n hn,
    induction n using nat.strong_induction_on with k ih,
    by_cases hkprime : is_prime k ,
    {
      use k,
      split,
      {assumption},
      apply symm,
      cases hkprime,
      dsimp at ih,
      have : (k / k) = 1, 
      { 
        apply nat.div_self,
        linarith
      },
      rw this,
      simp,
    },
    {
      rw is_prime at hkprime,
      push_neg at hkprime,
      by_cases kbig : k > 1,
      {
        specialize hkprime kbig,
        cases hkprime with d hd,
        rcases hd with ⟨h₁,h₂,h₃⟩,
        specialize ih d h₂,
        cases ih h₁ with p₁ hp₁,
        set m₁ := d / p₁ with hm₁,
        cases hp₁ with pprime h2,
        use [p₁, pprime],
        set m₂ := k / p₁ with hm₂,
        simp [hm₂],
        have : k % d + d * (k / d) = k, from nat.mod_add_div _ _,
        rw h₃ at this,
        simp at this,
        set n₁ := k / d with hn₁,
        rw h2 at this,
        conv_rhs {
          rw <-this,
          congr, skip,
          rw [mul_assoc, mul_comm],
          },
        cases pprime with hp₁ _,
        rw lemma_div m₁ n₁ p₁ (by {linarith}),
        rw <-this,
        ring,
      },
      {
        linarith,
      },
    },
end

theorem infinitude_of_primes : infinite primes :=
begin
  constructor,
  intro h,
  cases h with finprimes b,
  simp at b,
  set enum : primes → ℕ := λ p, p,
  set prod1 : ℕ := (∏ i in finprimes, enum i) with h,
  have prod_div : ∀ q ∈ primes, prod1 = q * (prod1 / q),
  {
    intros q hq,
    sorry,
  },
  set p := prod1 + 1 with hp,
  have p_is_not_divisible : ∀ q ∈ primes, p % q = 1,
  {
    intros q qprime,
    specialize prod_div q qprime,
    have : p % q + q * (p / q) = p, from nat.mod_add_div _ _,
    rw hp at *,
    rw prod_div,
    rw add_comm,
    simp,
    apply nat.mod_eq_of_lt,
    cases qprime,
    linarith,
  },
  have p_prime : is_prime p,
  {
    split,
    rw [hp, h],
    simp,
    {sorry},
    {
      intro h,
      rcases h with ⟨n, ⟨h₁,h₂,h₃⟩⟩,
      rcases has_prime_div n h₁ with ⟨ q, ⟨ hq1, hq2⟩ ⟩ ,
      suffices : p % q = 0,
      {
        specialize p_is_not_divisible q hq1,
        linarith,
      },
      {
        cases hq1 with qpos _,
        refine (div_div p q qpos).2 _,
        obtain H := (div_div p n h₁).1 h₃,
        rw hq2 at H,
        rcases H with ⟨ k₁, hk₁⟩,
        use k₁ * (n / q),
        rw hk₁,
        ring,
      }
    }
  },
  have p_is_not_prime : ¬is_prime p,
  {
    by_contra,
    specialize p_is_not_divisible p _,
    swap,
    {exact p_prime},
    simp at p_is_not_divisible,
    contradiction
  },
  contradiction,
end 

-- example : ¬is_prime 4005 := 
-- begin 
--   apply multiples_are_not_prime 3,
--   {by {split,linarith,refl}},
--   linarith,
-- end 


-- variables a b : Type*
-- variables f : a → b
-- variables x : a
-- variables y : b
-- example {f : a → b} : (∀ (y : b), ∃ (x : a), f(x) = y) → (∃ g : b → a, ∀ (y : b), f (g (y)) = y) :=
-- begin 
--   introv h₁,
--   split,
--   all_goals 
--   { 
--     assume y, 
--     have ex : ∃ (x : a), f x = y, from h₁ y,
--     cases ex,
--   },
--   sorry
-- end

















