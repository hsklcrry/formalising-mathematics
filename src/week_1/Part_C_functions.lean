import tactic

-- injective and surjective functions are already in Lean.
-- They are called `function.injective` and `function.surjective`.
-- It gets a bit boring typing `function.` a lot so we start
-- by opening the `function` namespace

open function

-- We now move into the `xena` namespace

namespace xena

-- let X, Y, Z be "types", i.e. sets, and let `f : X → Y` and `g : Y → Z`
-- be functions

variables {X Y Z : Type} {f : X → Y} {g : Y → Z}

-- let a,b,x be elements of X, let y be an element of Y and let z be an
-- element of Z

variables (a b x : X) (y : Y) (z : Z)

/-!
# Injective functions
-/

-- let's start by checking the definition of injective is
-- what we think it is.

lemma injective_def : injective f ↔ ∀ a b : X, f a = f b → a = b :=
begin
  -- true by definition
  refl
end

-- You can now `rw injective_def` to change `injective f` into its definition.

-- The identity function id : X → X is defined by id(x) = x. Let's check this

lemma id_def : id x = x :=
begin
  -- true by definition
  refl
end

-- you can now `rw id_def` to change `id x` into `x`

/-- The identity function is injective -/
lemma injective_id : injective (id : X → X) :=
begin
  rw injective_def,
  intros a b,
  rw id_def, rw id_def,
  tauto,
end

-- function composition g ∘ f is satisfies (g ∘ f) (x) = g(f(x)). This
-- is true by definition. Let's check this

lemma comp_def : (g ∘ f) x = g (f x) :=
begin
  -- true by definition
  refl
end

/-- Composite of two injective functions is injective -/
lemma injective_comp (hf : injective f) (hg : injective g) : injective (g ∘ f) :=
begin
  -- you could start with `rw injective_def at *` if you like.
  -- In some sense it doesn't do anything, but it might make you happier.
  rw injective_def at *,
  intros a b,
  intro h,
  rw [comp_def, comp_def] at h,
  apply hf a b,
  apply hg _ _,
  exact h,
end

/-!

### Surjective functions

-/

-- Let's start by checking the definition of surjectivity is what we think it is

lemma surjective_def : surjective f ↔ ∀ y : Y, ∃ x : X, f x = y :=
begin
  -- true by definition
  refl
end

/-- The identity function is surjective -/
lemma surjective_id : surjective (id : X → X) :=
begin
  -- you can start with `rw surjective_def` if you like.
  rw surjective_def,
  intro y,
  use y,
  exact id_def _,
end

-- If you started with `rw surjective_def` -- try deleting it.
-- Probably your proof still works! This is because
-- `surjective_def` is true *by definition*. The proof is `refl`.

-- For this next one, the `have` tactic is helpful.

/-- Composite of two surjective functions is surjective -/
lemma surjective_comp (hf : surjective f) (hg : surjective g) : surjective (g ∘ f) :=
begin
  rw surjective_def at *,
  intro z,
  cases hg z with y hgy,
  cases hf y with x hfx,
  use x,
  show g(f(x)) = z,
  rw [hfx, hgy]
end

/-!

### Bijective functions

In Lean a function is defined to be bijective if it is injective and surjective.
Let's check this.

-/

lemma bijective_def : bijective f ↔ injective f ∧ surjective f :=
begin
  -- true by definition
  refl
end

-- You can now use the lemmas you've proved already to make these
-- proofs very short.

/-- The identity function is bijective. -/
lemma bijective_id : bijective (id : X → X) :=
begin
  split,
  exact injective_id,
  exact surjective_id
end

/-- A composite of bijective functions is bijective. -/
lemma bijective_comp (hf : bijective f) (hg : bijective g) : bijective (g ∘ f) :=
begin
  split,
  {
    apply injective_comp,
    exact hf.1,
    exact hg.1
  },
  {
    apply surjective_comp,
    exact hf.2,
    exact hg.2
  }
end

end xena
