import week_7.Part_A_quotients
import week_7.Part_B_universal_property

/-

# `Z ≃ ℤ` 

Let's use the previous parts to show that Z and ℤ are isomorphic.

-/

-- Let's define pℤ to be the usual subtraction function ℕ² → ℤ
def pℤ (ab : N2) : ℤ := (ab.1 : ℤ) - ab.2

@[simp] lemma pℤ_def (a b : ℕ) : pℤ (a, b) = (a : ℤ) - b := rfl

-- Start with `intro z, apply int.induction_on z` to prove this.
theorem pℤsurj : function.surjective pℤ :=
begin
  intro z,
  apply int.induction_on z,
  {use (0,0), refl,},
  {
    intro i,
    intro h,
    rcases h with ⟨x,hx⟩,
    cases x,
    use (x_fst + 1, x_snd),
    rw <-hx,
    unfold pℤ,
    dsimp,
    ring,
  },
  {
    intros i h,
    rcases h with ⟨x,hx⟩,
    cases x,
    use (x_fst, x_snd + 1),
    rw <-hx,
    unfold pℤ,
    dsimp,
    ring,
  },
end

-- The fibres of pℤ are equivalence classes.
theorem pℤequiv (ab cd : N2) : ab ≈ cd ↔ pℤ ab = pℤ cd :=
begin
  unfold pℤ,
  split,
  {
    intro h,
    cases ab,
    cases cd,
    simp [refl] at h ⊢,
    linarith,
  },
  {
    intro h,
    simp,
    linarith,
  }
end

-- It's helpful to have a random one-sided inverse coming from surjectivity
noncomputable def invp : ℤ → N2 :=
λ z, classical.some (pℤsurj z)

-- Here's the proof that it is an inverse.
@[simp] theorem invp_inv (z : ℤ) : pℤ (invp z) = z :=
classical.some_spec (pℤsurj z)

-- Now we can prove that ℤ and pℤ are universal.
theorem int_is_universal : is_universal ℤ pℤ :=
begin
  split,
  {intros x y h, exact (pℤequiv x y).1 h},
  {
    intros,
    use (f ∘ invp),
    split,
    {
      ext z,
      apply h,
      apply (pℤequiv _ _).2,
      simp,
    },
    {
      intros k h,
      apply symm,
      calc f ∘ invp = (k ∘ pℤ) ∘ invp   : by rw h
                ... = k ∘ (pℤ ∘ invp)   : by refl
                ... = k ∘ id            : by {ext x, simp}
                ... = k                 : by {simp},
    },
  }
end

-- and now we can prove they're in bijection
noncomputable example : ℤ ≃ Z :=
universal_equiv_quotient _ _ _ int_is_universal 
