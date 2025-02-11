import tactic

-- Let `Ω` be a "big underlying set" and let `X` and `Y` and `Z` be subsets

variables (Ω : Type) (X Y Z : set Ω) (a b c x y z : Ω)

namespace xena

/-!

# subsets

Let's think about `X ⊆ Y`. Typeset `⊆` with `\sub` or `\ss`
-/

-- `X ⊆ Y` is the same as `∀ a, a ∈ X → a ∈ Y` , by definition.

lemma subset_def : X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y :=
begin
  -- true by definition
  refl
end

lemma subset_refl : X ⊆ X :=
begin
  rw subset_def _ X X,
  --intro a,
  tauto,
end

lemma subset_trans (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z :=
begin
  -- If you start with `rw subset_def at *` then you
  -- will have things like `hYZ : ∀ (a : Ω), a ∈ Y → a ∈ Z`
  -- You need to think of `hYZ` as a function, which has two
  -- inputs: first a term `a` of type `Ω`, and second a proof `haY` that `a ∈ Y`.
  -- It then produces one output `haZ`, a proof that `a ∈ Z`.
  -- You can also think of it as an implication:
  -- "if a is in Ω, and if a ∈ Y, then a ∈ Z". Because it's an implication,
  -- you can `apply hYZ`. This is a really useful skill!
  rw subset_def at *,
  intro a,
  intro ax,
  apply hYZ,
  apply hXY,
  assumption
end

/-!

# Equality of sets

Two sets are equal if and only if they have the same elements.
The name of this theorem is `set.ext_iff`.
-/

example : X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y) :=
begin
  exact set.ext_iff
end

-- In practice, you often have a goal `⊢ X = Y` and you want to reduce
-- it to `a ∈ X ↔ a ∈ Y` for an arbitary `a : Ω`. This can be done with
-- the `ext` tactic. 


lemma subset.antisymm (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y :=
begin
  -- start with `ext a`,
  ext a,
  split,
  {apply hXY},
  {apply hYX}
end

/-!

### Unions and intersections

Type `\cup` or `\un` for `∪`, and `\cap` or `\i` for `∩`

-/

lemma union_def : a ∈ X ∪ Y ↔ a ∈ X ∨ a ∈ Y :=
begin
  -- true by definition
  refl,
end

lemma inter_def : a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y :=
begin
  -- true by definition
  refl,
end


-- You can rewrite with those lemmas above if you're not comfortable with
-- assuming they're true by definition.

-- union lemmas

lemma union_self : X ∪ X = X :=
begin
  ext a,
  rw union_def,
  tauto,
end

lemma subset_union_left : X ⊆ X ∪ Y :=
begin
  rw subset_def,
  intro a,
  rw union_def,
  apply or.intro_left,
end

lemma subset_union_right : Y ⊆ X ∪ Y :=
begin
  intro a,
  intro haX,
  rw union_def,
  right,
  assumption
end

lemma union_subset_iff : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
begin
  split,
  {
    intro h,
    --rw subset_def at *,
    split,
    {
      intro a, 
      intro ax, 
      suffices hxy : X ⊆ X ∪ Y, 
      {
        apply h, apply hxy, assumption
      }, 
      exact subset_union_left _ _ _ 
    },
    {
      intro a, 
      intro ay, 
      suffices hxy : Y ⊆ X ∪ Y, 
      {
        apply h, apply hxy, assumption
      }, 
      exact subset_union_right _ _ _ 
    }
  },
  {
    rintro ⟨h₁,h₂⟩,
    intro a,
    rw subset_def at *,
    rw union_def,
    intro h,
    apply or.elim h (h₁ a) (h₂ a)
  }
end

variable (W : set Ω)

lemma union_subset_union (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z :=
begin
  intro a,
  rw union_def at *,
  rw union_def at *,
  rw subset_def at *,
  apply or.imp (hWX a) (hYZ a),
end

lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z :=
begin
  intro a,
  rw union_def at *,
  rw union_def at *,
  rw subset_def at hXY,
  apply or.imp_left (hXY a),
end

-- etc etc

-- intersection lemmas

lemma inter_subset_left : X ∩ Y ⊆ X :=
begin
  intro a,
  rw inter_def,
  exact and.elim_left,
end

-- don't forget `ext` to make progress with equalities of sets

lemma inter_self : X ∩ X = X :=
begin
  ext a,
  rw inter_def,
  split,
  {exact and.left},
  {intro h, exact ⟨h,h⟩} 
end

lemma inter_comm : X ∩ Y = Y ∩ X :=
begin
  ext a,
  rw [inter_def, inter_def],
  exact and.comm,
end

lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
begin
  ext a,
  rw [inter_def, inter_def,inter_def, inter_def],
  rw and.assoc,
end

/-!

### Forall and exists

-/

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
begin
  split,
  {
    intro h,
    intro b,
    by_contra hb,
    have : ∃ (a : Ω), a ∈ X, existsi b, exact hb,
    contradiction,
  },
  {
      intro h,
      intro ex_x,
      cases ex_x with x xX,
      have : x ∉ X, exact h x,
      contradiction,
  }
end

example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
begin
  split,
  {
    intro h,
    by_contra h₂,
    apply h,
    intro a,
    by_contra hanX,
    apply h₂,
    use a,
  },
  {
    intro h,
    by_contra h₂,
    cases h with x hnX,
    apply hnX,
    exact h₂ x
  }
end

end xena

