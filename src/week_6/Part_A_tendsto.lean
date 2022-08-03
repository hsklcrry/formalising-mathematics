import order.filter.basic

/-

# tendsto

Here's an overview of the main definition we're learning today.

If `X` and `Y` are types, `φ : X → Y` is a function,
and `F : filter X` and `G : filter Y` are filters, then

`filter.tendsto φ F G`

is a true-false statement, which is pronounced something like
"`F` tends to `G` along `φ`". Of course we will `open filter`
in this file, so you can just write `tendsto φ F G`, or if
you like the dot notation you can even write `F.tendsto φ G`.

## Geometric meaning of `tendsto`.

Let's start by thinking about the easy case where `F` and `G`
are actually subsets of `X` and `Y` (that is, principal filters,
associated to sets which we will also call `F` and `G`). In this case,
`tendsto φ F G` simply means "`φ` restricts to a function
from `F` to `G`", or in other words `∀ x ∈ F, φ(x) ∈ G`.

There are two other ways of writing this predicate. The first
involves pushing a set forward along a map. If `F` is a subset of `X`
then let `φ(F)` denote the image of `F` under `φ`, that
is, the subset `{y : Y | ∃ x : X, φ x = y}` of `Y`.
Then `tendsto φ F G` simply means `φ(F) ⊆ G`.

The second involves pulling a set back along a map. If `G` is a subset
of `Y` then let `φ⁻¹(G)` denote the preimage of `G` under `φ`,
that is, the subset `{x : X | φ x ∈ G}` of `Y`. Then `tendsto φ F G`
simply means `F ⊆ φ⁻¹(G)`. 

This is how it all works in the case of sets. What we need to
do today is to figure out how to push forward and pull back
filters along a map `φ`. Once we have done this, then we can
prove `φ(F) ≤ G ↔ F ≤ φ⁻¹(G)` and use either one of these
as our definition of `tendsto φ F G` -- it doesn't matter which.

## Digression : adjoint functors.

The discussion below is not needed to be able to do this week's
problems, but it might provide some helpful background for some.
Also note that anyone who still doens't like the word "type" can
literally just change it for the word "set" (and change "term of
type" to "element of set"), which is how arguments
of the below kind would appear in the traditional mathematical
literature.

Partially ordered types, such as the type of subsets of a fixed
type `X` or the type of filters on `X`, are actually very simple
examples of categories. In general if `P` is a partially ordered type
and `x,y` are terms of type `P` then the idea is that we can
define `Hom(x,y)` to have exactly one element if `x ≤ y` is true,
and no elements at all if `x ≤ y` is false. The structure/axioms for
a category are that `Hom(x,x)` is supposed to have an identity
element, which follows from reflexivity of `≤`, and that one can
compose morphisms, which follows from transitivity of `≤`.
Antisymmetry states that if two objects are isomorphic (i.e.,
in this case, if `Hom(x,y)` and `Hom(y,x)` are both nonempty),
then they are equal. If `φ : X → Y` is a map of types, then
pushing forward subsets and pulling back subsets are both
functors from `set X` to `set Y`, because `S ⊆ T → φ(S) ⊆ φ(T)`
and `U ⊆ V → φ⁻¹(U) ⊆ φ⁻¹(V)`. The statement that
`φ(S) ≤ U ↔ S ≤ φ⁻¹(U)` is simply the statement that these functors
are adjoint to each other. Today we will define pushforward and
pullback of filters, and show that they are also a pair of
adjoint functors, but we will not use this language. In fact there
is a special language for adjoint functors in this simple situation:
we will say that pushforward and pullback form a Galois connection.

-/

/-

## Warm-up: pushing forward and pulling back subsets.

Say `X` and `Y` are types, and `f : X → Y`.

-/

variables (X Y : Type) (f : X → Y)

/-

### images

In Lean, the image `f(S)` of a subset `S : set X` cannot
be denoted `f S`, because `f` expects an _element_ of `X` as
an input, not a subset of `X`, so we need new notation.

Notation : `f '' S` is the image of `S` under `f`. Let's
check this.

-/

example (S : set X) : f '' S = {y : Y | ∃ x : X, x ∈ S ∧ f x = y} :=
begin
  -- true by definition
  refl
end

/-

### preimages

In Lean, the preimage `f⁻¹(T)` of a subset `T : set Y` cannot
be denoted `f⁻¹ T` because `⁻¹` is the inverse notation in group
theory, so if anything would be a function from `Y` to `X`,
not a function on subsets of `Y`. 

Notation : `f ⁻¹' T` is the preimage of `T` under `f`. Let's
check this.

Pro shortcut: `\-'` for `⁻¹'` 

-/

example (T : set Y) : f ⁻¹' T = {x : X | f x ∈ T} :=
begin
  -- true by definition
  refl
end

/-

I claim that the following conditions on `S : set X` and `T : set Y`
are equivalent:

1) `f '' S ⊆ T`
2) `S ⊆ f⁻¹' T`

Indeed, they both say that `f` restricts to a function from `S` to `T`.
Let's check this. You might find

`mem_preimage : a ∈ f ⁻¹' s ↔ f a ∈ s`

and 

-/

open set

example (S : set X) (T : set Y) : f '' S ⊆ T ↔ S ⊆ f⁻¹' T :=
begin
  split,
  {
    intros h x hx,
    have H : f(x) ∈ T,
    {apply h, use [x,hx]},
    exact H,
  },
  {
    intros h y hy,
    rcases hy with ⟨ x, hx, rfl ⟩,
    exact h hx,
  }
end

/-

## Pushing forward filters.

Pushing forward is easy, so let's do that first.
It's called `filter.map` in Lean.

We define the pushforward filter `map f F` on `Y` to be the
obvious thing: a subset of `Y` is in the filter iff `f⁻¹(Y)`
is in `F`. Let's check this is a filter.  

Reminder of some helpful lemmas:

In `set`:
`mem_set_of_eq : a ∈ {x : α | p x} = p a` -- definitional

In `filter`:
`univ_mem_sets : univ ∈ F`
`mem_sets_of_superset : S ∈ F → S ⊆ T → T ∈ F`
`inter_mem_sets : S ∈ F → T ∈ F → S ∩ T ∈ F`

-/

open filter

-- this is called `F.map f` or `filter.map f F` 
-- or just `map f F` if `filter` is open.
example (F : filter X) : filter Y :=
{ sets := {T : set Y | f ⁻¹' T ∈ F },
  univ_sets := begin
    exact univ_mem_sets,
  end,
  sets_of_superset := begin
    rintros x y hx hxy,
    dsimp at hx ⊢,
    apply mem_sets_of_superset hx,
    exact preimage_mono hxy,
  end,
  inter_sets := begin
    rintros x y hx hy,
    dsimp at *,
    apply inter_mem_sets,
    assumption,assumption
  end, }


-- this is `filter.mem_map` and it's true by definition.
-- It's useful in the form `rw mem_map` if you want to figure out
-- what's going on in a proof, but often you'll find you can
-- delete it at the end.
example (F : filter X) (T : set Y) : T ∈ F.map f ↔ f ⁻¹' T ∈ F :=
begin
  -- true by definition
  refl
end

-- Let's check that `map` satisfies some basic functorialities.
-- Recall that if your goal is to check two filters are
-- equal then you can use the `ext` tactic, e.g. with `ext S`.

-- pushing along the identity map id : X → X doesn't change the filter.
-- this is `filter.map_id` but see if you can prove it yourself.
example (F : filter X) : F.map id = F :=
begin
  ext x,
  rw filter.mem_map,
  dsimp,
  tauto,
end

-- pushing along g ∘ f is the same as pushing along f and then g
-- for some reason this isn't in mathlib, instead they have `map_map` which
-- has the equality the other way.
variables (Z : Type) (g : Y → Z)

-- this isn't in mathlib, but `filter.map_map` is the equality the other
-- way around. See if you can prove it yourself.
example (F : filter X) : F.map (g ∘ f) = (F.map f).map g :=
begin
  ext x,
  rw [filter.mem_map, filter.mem_map, filter.mem_map],
  dsimp,
  tauto,
end

open_locale filter -- for 𝓟 notation

-- pushing the principal filter `𝓟 S` along `f` gives `𝓟 (f '' S)`
-- this is `filter.map_principal` but see if you can prove it yourself.
example (S : set X) : (𝓟 S).map f = 𝓟 (f '' S) :=
begin
  ext x,
  rw [filter.mem_map, mem_principal_sets, mem_principal_sets],
  split,
  {intros h X hX, rcases hX with ⟨x, hx, rfl⟩, apply h, exact hx},
  {intros h y hy, apply h, use [y, hy]}  
end

/-

## tendsto

The definition: if `f : X → Y` and `F : filter X` and `G : filter Y`
then `tendsto f F G : Prop := map f F ≤ G`. It's pronounced something
like "`F` tends to `G` along `f`". This is a *definition* (it
has type `Prop`), not the proof of a theorem. It is a true-false statement
attached to `f`, `F` and `G`, it's a bit like saying "f is continuous at x"
or something like that, it might be true and it might be false.

The mental model you might want to have of the definition is that
`tendsto f F G` means that the function `f` restricts to a function
from the generalized set `F` to the generalized set `G`.

-/

-- this is `filter.tendsto_def`
example (F : filter X) (G : filter Y) :
  tendsto f F G ↔ ∀ T : set Y, T ∈ G → f ⁻¹' T ∈ F :=
begin
  -- true by definition
  refl
end

-- Let's make a basic API for `tendsto`

-- this is `tendsto_id` but see if you can prove it yourself.
example (F : filter X) : tendsto id F F :=
begin
  rw filter.tendsto_def,
  dsimp,
  tauto,
end

-- this is `tendsto.comp` but see if you can prove it yourself
example (F : filter X) (G : filter Y) (H : filter Z)
  (f : X → Y) (g : Y → Z)
  (hf : tendsto f F G) (hg : tendsto g G H) : tendsto (g ∘ f) F H :=
begin
  rw filter.tendsto_def at *,
  intros s hs,
  specialize hg s hs,
  specialize hf _ hg,
  exact hf
end

-- I would recommend looking at the model answer to this one if
-- you get stuck.
lemma tendsto_comp_map (g : Y → Z) (F : filter X) (G : filter Z) :
  tendsto (g ∘ f) F G ↔ tendsto g (F.map f) G :=
begin
  rw [filter.tendsto_def, filter.tendsto_def],
  refl,
end

/-

## Pulling back filters

We don't use this in the next part.

Say `f : X → Y` and `G : filter Y`, and we want a filter on `X`. Let's make a
naive definition. We want a collection of subsets of `X` corresponding to the
filter obtained by pulling back `G` along `f`. When should `S : set X` be
in this filter? Perhaps it is when `f '' S ∈ G`. However, there is no reason
that the collection of `S` satisfying this property should be a filter
on `X`. For example, there is no reason to espect that `f '' univ ∈ G`
if `f` is not surjective. Our naive guess doesn't work.

Here's a way of fixing this, by coming up with a less naive guess which
is informed by our mental model. Remember that our model of a filter `G` is some
kind of generalised notion of a set. If `T : set Y` then `T ∈ G` is supposed to
mean that the "set" `G` is a subset of `T`. So this should imply
that `f⁻¹(G) ⊆ f⁻¹(T)`. In particular, if `T ∈ G` and `f⁻¹(T) ⊆ S` then this
should mean `f⁻¹(G) ⊆ S` and hence `S ∈ f⁻¹(G)`. Let's try this condition
(defining `S ∈ f⁻¹(G)` to mean `∃ T ∈ G, f⁻¹(T) ⊆ S`) and see if it works.

Random useful lemmas (you might be getting to the point where you can
guess the names of the lemmas):

`subset_univ S : S ⊆ univ`
`subset.trans : A ⊆ B → B ⊆ C → A ⊆ C`
-/

-- this is called filter.comap
example (G : filter Y) : filter X :=
{ sets := {S : set X | ∃ T ∈ G, f ⁻¹' T ⊆ S},
  univ_sets := begin
    dsimp,
    use univ,
    rcases G,
    use G_univ_sets,
    apply subset_univ,
  end,
  sets_of_superset := begin
    intros x y hx hxy,
    dsimp at hx ⊢,
    rcases hx with ⟨ S, hS, hfS⟩,
    use [S, hS],
    apply subset.trans hfS hxy,
  end,
  inter_sets := begin
    intros x y hx hy,
    dsimp at *,
    rcases hx with ⟨ S, hS, hS2 ⟩,
    rcases hy with ⟨ T, hT, hT2 ⟩,
    use S ∩ T,
    split,
    {exact inter_mem_sets hS hT},
    {dsimp, exact inter_subset_inter hS2 hT2}
  end }

-- Let's call this mem_comap
lemma mem_comap (f : X → Y) (G : filter Y) (S : set X) :
  S ∈ comap f G ↔ ∃ T ∈ G, f ⁻¹' T ⊆ S :=
begin
  -- true by definition
  refl
end

-- If you want to, you can check some preliminary properties of `comap`. 

-- this is comap_id
example (G : filter Y) : comap id G = G :=
begin
  ext s,
  rw mem_comap,
  dsimp,
  split,
  {rintros ⟨a, b, hb⟩, exact mem_sets_of_superset b hb},
  {intros hs, use [s, hs]}
end

-- this is comap_comap but the other way around
lemma comap_comp (H : filter Z) : comap (g ∘ f) H = comap f (comap g H) :=
begin
  ext s,
  rw [mem_comap,mem_comap],
  split,
  {
    rintros ⟨T, hT, hT2⟩,
    use [g ⁻¹' T],
    rw mem_comap,
    use [T, hT],
    exact hT2,
  },
  {
    rintros ⟨T, hT, hT2⟩,
    rcases hT with ⟨R, ⟨hR, hR2⟩⟩,
    use [R, hR],
    refine subset.trans _ hT2,
    refine preimage_mono hR2,
  }
end

-- this is comap_principal. Remember `mem_principal_sets`! It's true by definition...
example (T : set Y) : comap f (𝓟 T) = 𝓟 (f ⁻¹' T) :=
begin
  ext t,
  rw mem_comap,
  split,
  {
    rintros ⟨S, hS, hS2⟩,
    refine subset.trans _ hS2,
    refine preimage_mono hS,
  },
  {
    intro h,
    use [T], 
    use mem_principal_self T,
    exact h,
  }
end


-- This is the proof that `map f` and `comap f` are adjoint functors,
-- or in other words form a Galois connection. It is the "generalised set"
-- analogue of the assertion that if S is a subset of X and T is a subset of Y
-- then f(S) ⊆ T ↔ S ⊆ f⁻¹(T), these both being ways to say that `f` restricts
-- to a function from `S` to `T`.
lemma filter.galois_connection (F : filter X) (G : filter Y) : 
  map f F ≤ G ↔ F ≤ comap f G :=
begin
  split,
  {
    rintros hf,
    rintros S ⟨T, ⟨hT,fTS⟩⟩,
    apply mem_sets_of_superset _ fTS,
    apply hf,
    exact hT,
  },
  {
    intro hf,
    rintros S hS,
    apply hf,
    rw mem_comap,
    use [S, hS],
  }
end

-- indeed, `map f` and `comap f` form a Galois connection.
example : galois_connection (map f) (comap f) :=
filter.galois_connection X Y f 
