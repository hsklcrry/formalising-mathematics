import tactic -- import the tactics
import data.set.basic -- import the sets
import data.set.lattice -- infinite unions and intersections

/-

# Sets

## Introduction

In contrast to group theory, where we made our own definition
of a group and developed our own API (i.e. the lemmas we need
to prove basic results in group theory), here we will use Lean's API.

The first thing to learn is that this is not some development
of set theory, or ZFC, or whatever "set theory" brings to mind.
This is all about the theory of _subsets_ of a set, or, more
precisely, subsets of a type.

Just like `subgroup G` was the type of subgroups of `G`, 
`set X` is the type of subsets of `X`. Don't ask me why it's
not called `subset X`. I guess the idea is that if `S : set X`
then `S` is a set of elements of `X` or, more precisely, 
a set of terms of `X`.

And, also like `subgroup G`, if `S : set X` then `S` is a term,
not a type. This is a bit weird because in type theory our
model is that types are sets, and terms are their elements, 
and `a : X` means that `a` is an element of `X`. 

The way subsets work is like this. If `S : set X` and if `a : X`
then there's a predicate `a ∈ S`, which means that `a` is in
the subset `S` of `X`. Note that the _type_ of `a` is still `X`,
it's just that `a` happens to be in `S` as well. This is why we
can't have `S` as a type: then we would want to write `a : S`
and `a : X`, but terms in type theory can only have one type.

## Implementation

You don't need to know about implentation -- that's the point of the API.
Any new definition, like `set X`, should be accessed and reasoned with
using its API, the collection of lemmas that comes with it. But here's
what's actually going on.

Under the hood, if `S : set X` then `S` is a function from `X` to `Prop`. 
The idea is that a subset of `X` is represented internally as a function
to `{true, false}` which sends all the elements of `S` to `true` and
all the other elements to `false`. In fact `set X := X → Prop` is
the internal definition of `set`. Internally, the statement `a ∈ S`
is just encoded as the proposition `S a`.

## Notation

There is a lot of it.

Say `(X Y : Type)`

The empty set is `∅ : set X`. Hover over the symbol to find out
how to write it in Lean.

The set corresponding to all of `X` is `set.univ : set X`, or
just `univ : set X` if you have written `open set` earlier in the file.

If `S : set X` then its complement is `Sᶜ : set X`.

Now say `f : X → Y`.

If `S : set X` then `f '' S : set Y` is the image of `S`.

If `T : set Y` then `f ⁻¹' T : set X` is the preimage of `T`.

The range of `f` could be written `f '' univ`, however there
is also `range f`. 

Finally remember `subset_def : S ⊆ T ↔ ∀ x, x ∈ S → x ∈ T`

-/

variables (X Y Z : Type) (f : X → Y) (g : Y → Z) (S : set X) (y : Y)

open set

/-!

## image

`y ∈ f '' S` is definitionally equal to `∃ x : X, x ∈ S ∧ f x = y`,
but if you want to rewrite to change one to the other,
we have

`mem_image f S y : y ∈ f '' S ↔ ∃ (x : X), x ∈ S ∧ f x = y`

-/

-- here are four proofs of image_id, each taking more short cuts 
-- than the last. In practice I might write the first proof
-- and then "golf" it down so it becomes closer to the fourth one.
-- Go through the first proof and then take a look at some
-- of the shortcuts I introduce.

lemma image_id (S : set X) : id '' S = S :=
begin
  ext x,
  split,
  { intro h,
    rw mem_image at h,
    cases h with y hy,
    cases hy with hyS hid,
    rw id.def at hid,
    rw ← hid,
    exact hyS },
  { intro hxS,
    rw mem_image,
    use x,
    split,
    { exact hxS },
    { rw id.def } }
end

example : id '' S = S :=
begin
  ext x,
  split,
  { intro h,
    -- don't need to `rw mem_image` because it's definitional
    -- rcases can do multiple `cases` at once. Note that ⟨a, b, c⟩ = ⟨a, ⟨b, c⟩⟩
    rcases h with ⟨y, hyS, hid⟩,
    -- don't need to `rw id.def` because it's definitional
    rw ← hid,
    exact hyS },
  { intro hxS,
    use x,
    -- if the goal is `⊢ P ∧ Q` and you have a proof of `P`, you can `use` it
    use hxS,
    -- `⊢ id x = x` is true by definition
    refl } 
end 

example : id '' S = S :=
begin
  ext x,
  split,
  { -- the `rintro` tactic will do `intro, cases`
    -- and will even do both `cases` at once!
    rintro ⟨y, hyS, hid⟩,
    rw ← hid,
    exact hyS },
  { intro hxS,
    -- two `use`s can go together
    use [x, hxS], 
    refl }
end

-- this is the shortest explicit tactic proof I know which doesn't
-- cheat and use the corresponding lemma in Lean's maths library:
example : id '' S = S :=
begin
  ext x,
  split,
  { -- `hid` says `(something) = y` so why not just _define_ y to be this!
    rintro ⟨y, hyS, rfl⟩, -- rfl deletes `y` from the context and subs in `id x`
    exact hyS },
  { intro hxS,
  -- we can just build this term
    exact ⟨x, hxS, rfl⟩ },
end

-- Other proofs which won't teach you as much:

example : id '' S = S :=
begin
  -- it's in the library already
  apply image_id',
end

example : id '' S = S := 
begin
  simp -- `image_id'` is tagged `@[simp]` so `simp` finds it.
end

-- This tactic also finds `image_id'` in the library
example : id '' S = S := 
begin
  finish,
end

-- So does this one.
example : id '' S = S := 
begin
  tidy
end

-- The disadvantages of these last few proofs : (a) `finish` and `tidy` are
-- slow (b) they won't teach you much and (c) if the theorems are not
-- already in Lean's maths library then the tactics might not be of much use.

-- Let's see what you make of these lemmas about sets. 

lemma image_comp (S : set X) : (g ∘ f) '' S = g '' (f '' S) :=
begin
  ext x,
  split,
  {
    rintro ⟨ x,h2,rfl⟩,
    simp,
    use x,
    split, 
    assumption,
    refl,
  },
  {
    rintro ⟨ x, h1, rfl ⟩,
    simp, 
    rcases h1 with ⟨ s, hs, rfl ⟩,
    use [s, hs],
  }
end

open function

-- don't forget you can use `dsimp` to tidy up evaluated lambdas
lemma image_injective : injective f → injective (λ S, f '' S) :=
begin
  intro hinj,
  intros A B heq,
  dsimp at heq,
  ext x,
  split,
  {
    intro hxA,
    have : f x ∈ f '' A, 
    use [x, hxA],
    rw heq at *,
    rcases this with ⟨b, hb, hf ⟩,
    specialize hinj hf,
    rw <- hinj,
    exact hb
  },
  {
    intro hxB,
    have : f x ∈ f '' B, 
    use [x, hxB],
    rw <- heq at *,
    rcases this with ⟨a, ha, hf ⟩,
    specialize hinj hf,
    rw <- hinj,
    exact ha
  }
end

/-!

## preimage

The notation : `f ⁻¹' T`. The useful lemma:

`mem_preimage : x ∈ f ⁻¹' T ↔ f x ∈ T`

but in fact both sides are equal by definition.

-/

example (S : set X) : S = id ⁻¹' S :=
begin
  refl,
end

-- Do take a look at the model solutions to this one (which I'll upload 
-- after the workshop )

example (T : set Z) : (g ∘ f) ⁻¹' T = f ⁻¹' (g ⁻¹' T) :=
begin
  refl,
end

lemma preimage_injective (hf : surjective f) : injective (λ T, f ⁻¹' T) :=
begin
  sorry
end

lemma image_surjective (hf : surjective f) : surjective (λ S, f '' S) :=
begin
  sorry
end

lemma preimage_surjective (hf : injective f) : surjective (λ S, f ⁻¹' S) :=
begin
  sorry
end

/-!

## Union

If `(ι : Type)` and `(F : ι → set X)` then the `F i` for `i : ι`
are a family of subsets of `X`, so we can take their union.
This is `Union F` (note the capital U -- small u means union of two things,
capital means union of arbitrary number of things).
But the notation used in the lemmas is `⋃ (i : ι), F i`.

The key lemma you need to prove everything is that something is
an element of the union iff it's an element of one of the sets.

`mem_Union : (x ∈ ⋃ (i : ι), F i) ↔ ∃ j : ι, x ∈ F j`

-/

variables (ι : Type) (F : ι → set X) (x : X)

lemma image_Union (F : ι → set X) (f : X → Y) :
  f '' (⋃ (i : ι), F i) = ⋃ (i : ι), f '' (F i) :=
begin
  sorry
end

/-!

## bUnion

If as well as `F : ι → set X` you have `Z : set ι` then you might
just want to take the union over `F i` as `i` runs through `Z`.
This is called a "bounded union" or `bUnion`, and 
the notation is `⋃ (i ∈ Z), F i`.

The lemma for elements of a bounded union is:

`mem_bUnion_iff : (x ∈ ⋃ (i ∈ J), F i) ↔ ∃ (j ∈ J), x ∈ F j`

-/

lemma preimage_bUnion (F : ι → set Y) (Z : set ι) :
  f ⁻¹' (⋃ (i ∈ Z), F i) = ⋃ (i ∈ Z), f ⁻¹' (F i) :=
begin
  sorry
end