import tactic
/-

# Quotients

The quotient of a type by an equivalence relation.

## Overview

A binary relation on a type `X` is just a function `r : X → X → Prop`,
that is, a true-false statement attached to each pair of elements of `X`.

If `r` is also reflexive, symmetric and transitive, we say it is an
equivalence relation. We will use the standard notation `x ≈ y`
for `r x y` below.

Given a type `X` and an equivalence relation `≈` on it, the type `clX` of
equivalence classes for `≈` comes equipped with a canonical function
`X → clX` (sending an element to its equivalence class), and it also satisfies
a universal property, namely that to give a map from `clX` to a type `T`
is to give a map `X → T` which is constant on equivalence classes.

Note however that other types other than the type of equivalence classes
may also satisfy this universal property. For example if we start with
a type `X` and a surjection `p : X → Y` and then define an equivalence
relation on `X` by `x₁ ≈ x₂ ↔ p x₁ = p x₂` then `Y` satisfies the same
universal property. In general it is a fact in mathematics that things
which define universal properties are unique up to unique isomorphism,
and things like the type of equivalence classes are just a *model* for
this general concept of quotient.

Lean does not use the equivalence class model when doing quotients.
Here's how it does it. The type `setoid X` is defined to be the type
of equivalence relations on `X`. If `s : setoid X` is an equivalence relation
then Lean defines `quotient s` to be a new type which satisfies the
universal property of quotients. Let us spell out what this means.
Firstly, it means that there is a map `p : X → quotient s`, and
secondly it means that to give a map `f : quotient s → T` is to
give `f ∘ p : X → T`, a map which is constant on equivalence classes.

In this file we will learn the various useful functions which Lean has
for dealing with quotients -- that is, the key definitions and theorems
which mathematicians use, sometimes subconsciously, when dealing with
quotients. We will learn them by explicitly working through an
example, namely the case where `X = ℕ²` and `(a,b) ≈ (c,d) ↔ a + d = c + b`. 
In this case, the quotient is a model for the integers.

## More on universal properties.

Recall that if `X` and `T` are types, then `X → T` denotes the *type*
of functions from `X` to `T`. A mathematician might call this
type `Hom(X,T)`. A term `f : X → T` of this type is just a function
from `X` to `T`.

Let us now spell out the universal property more carefully.
Given a type `X` and an equivalence relation `≈` on `X`, we say
that a function `f : X → T` is *constant on equivalence classes*,
(or `≈`-equivariant for short), if `∀ x y : X, x ≈ y → f x = f y`. 

We say that a pair `(Q, p)` consisting of a type `Q` and a
function `p : X → Q` are a *quotient* of `X` by `≈`
if `p` is constant on equivalence classes, and furthermore `p`
is *initial* with repect to this property. What does this mean?
Let me spell this out. 

Let `(Q, p)` be a quotient of `X` by `≈`. Note first that if `T` is any
type and `g : Q → T` is any function, then `f := g ∘ p : X → T` is
constant on equivalence classes (because `p` is). Being *initial* is the claim
that this construction, starting with a function `g : Q → T` and
giving us a function `f : X → T` which is `≈`-equivariant,
is a *bijection* between `Q → T` and the subset of `X → T`
consisting of `≈`-equivariant functions. In diagrams, if `f` is
constant on equivalence classes, then there's a unique `g` which
fills in the diagram.

          f
    X ---------> T
    |          /\
    |        /
    | p    / ∃!g
    |    /
    |  /
    \/
    Q


One can easily check that the type of equivalence classes for `≈` satisfies
this universal property, with `p` being the map sending a term of type `X`
to its equivalence class. One can think of the type of equivalence classes
as a "model" for the quotient, in the same way that you might have seen
a model for the tensor product `V ⊗ W` of two vector spaces given
as a quotient of the vector space generated by pairs `(v,w)` by the subspace
generated by an appropriate collection of relations, or a model for
the localisation `R[1/S]` of a commutative ring at a multiplicative
subset given by `R × S` modulo a certain equivalence relation. Models
are useful. A model of an `n`-dimensional real vector space is obtained
by choosing a basis; then it can be identified with `ℝⁿ` enabling explicit
computations to be done. 

But there are many other models for quotients. For example let's
say `X` and `Q` are any types, and `f : X → Q` is any surjection at all.
Define `≈` on `X` by `x ≈ y ↔ f x = f y`. It is easy to check that `Q` is a
quotient of `X` by `≈` simply because `Q` naturally bijects with the
equivalence classes of `≈`.

Lean does not use equivalence classes in its definition of the quotient
of `X` by `≈`. It chooses a different model. It is an opaque model, meaning
that you cannot actually see what the terms are.
But Lean and mathlib give you a very solid API for the quotient.
In particular, the quotient satisfies the universal property, so one
can prove that it bijects with the type of equivalence classes on `X`.
However, after a while one moves away from the "equivalence class"
way of thinking, and starts thinking more abstractly about quotients,
and so ultimately one does not really need this bijection at all.

You might wonder why Lean does not use the type of equivalence classes.
The reason is not a mathematical one -- it is simply to do with an
implementation issue which I will mention later.

Here is a guided tour of the API for Lean's quotients, worked out for
a specific example -- the integers, as a quotient of ℕ² by the
equivalence relation `(a,b) ≈ (c,d) ↔ a + d = c + b.`

-/

-- N2 is much easier to type than `ℕ × ℕ` 
abbreviation N2 := ℕ × ℕ

namespace N2 -- all the functions below will be N2.something

-- Hmm, I guess I should run you through the API for products `×`. 

/-

### products

The product of two types `X` and `Y` is `prod X Y`, with notation `X × Y`.
Hover over `×` to find out how to type it.

-/
section product

-- to make a term of a product, use round brackets.
def foo : N2 := (3,4)

-- To extract the first term of a product, use `.1` or `.fst`

example : foo.1 = 3 := 
begin
  -- true by definition.
  refl
end

example : foo.fst = 3 :=
begin
  refl
end

-- similarly use `.2` or `.snd` to get the second term

example : foo.snd = 4 := rfl -- term mode reflexivity of equality

-- The extensionality tactic works for products: a product is determined
-- by the two parts used to make it.
example (X Y : Type) (s t : X × Y) (h1 : s.fst = t.fst) (h2 : s.snd = t.snd) :
  s = t :=
begin
  ext,
  { exact h1 },
  { exact h2 }
end

-- you can uses `cases x` on a product if you want to take it apart into
-- its two pieces
example (A B : Type) (x : A × B) : x = (x.1, x.2) :=
begin
  -- note that this is not yet `refl` -- you have to take `x` apart. 
  cases x with a b,
  -- ⊢ (a, b) = ((a, b).fst, (a, b).snd)
  dsimp only, -- to tidy up: this replaces `(a, b).fst` with `a`.
  -- ⊢ (a, b) = (a, b)
  refl,
end

end product

/-

## Worked example: ℤ as a quotient of ℕ²  

There's a surjection `ℕ × ℕ → ℤ` sending `(a,b)` to `a - b` (where here
`a` and `b` are regarded as integers). One checks easily that `(a,b)`
and `(c,d)` are sent to the same integer if and only if `a + d = b + c`.
Conversely one could just define an equivalence relation on ℕ × ℕ
by `ab ≈ cd ↔ ab.1 + cd.2 = cd.1 + ab.2` and then redefine ℤ -- or more
precisely define a second ℤ -- to be the quotient
by this equivalence relation. Let's set up this equivalence relation
and call the quotient `Z`. Recall we're using `N2` to mean `ℕ × ℕ`.

-/


def r (ab cd : N2) : Prop :=
ab.1 + cd.2 = cd.1 + ab.2

-- This is a definition so let's make a little API for it.
-- It's nice to be able to `rw` to get rid of explicit occurrences of `r`.
-- So let's make two lemmas suitable for rewriting.

lemma r_def (ab cd : N2) : r ab cd ↔ ab.1 + cd.2 = cd.1 + ab.2 :=
begin
  refl
end

-- This one is more useful if you've already done `cases` on the pairs.
lemma r_def' (a b c d : ℕ) : r (a,b) (c,d) ↔ a + d = c + b :=
begin
  refl
end

def r_refl : reflexive r :=
begin
  -- you can start with `unfold reflexive` if you want to see what
  -- you're supposed to be proving here.
  sorry,
end

-- hint: `linarith` is good at linear arithmetic. 
def r_symm : symmetric r :=
begin
  sorry
end

def r_trans : transitive r :=
begin
  sorry
end

-- now let's give N2 a setoid structure coming from `r`.
-- In other words, we tell the type class inference system
-- about `r`. Let's call it `setoid` and remember
-- we're in the `N2` namespace, so its full name
-- is N2.setoid
instance setoid : setoid N2 := ⟨r, r_refl, r_symm, r_trans⟩

-- Now we can use `≈` notation

example (x y : N2) : x ≈ y ↔ r x y :=
begin
  -- true by definition
  refl
end

-- `r x y` and `x ≈ y` are definitionally equal but not syntactically equal,
-- rather annoyingly, so we need two more lemmas enabling us to rewrite.
-- Let's teach them to `simp`, because they're the ones we'll be using
-- in practice.

@[simp] lemma equiv_def (ab cd : N2) : ab ≈ cd ↔ ab.1 + cd.2 = cd.1 + ab.2 :=
begin
  refl
end

@[simp] lemma equiv_def' (a b c d : ℕ) : (a,b) ≈ (c,d) ↔ a + d = c + b :=
iff.rfl -- term mode variant

end N2

open N2

-- Now we can take the quotient!
def Z := quotient N2.setoid

namespace Z

-- And now we can finally start.

-- The map from N2 to Z is called `quotient.mk`
-- Recall `foo` is `(3,4)`

def bar : Z := quotient.mk foo -- bar is the image of `foo` in the quotient.
-- so it's morally -1.

-- Notation for `quotient.mk x` is `⟦x⟧`
example : bar = ⟦foo⟧ :=
begin
  refl
end

/-

## Z

We have a new type `Z` now, and a way of going from `N2`
to `Z` (`quotient.mk`, with notation `⟦ ⟧`). 

Here then are some things we can think about:

(1) How to prove the universal property for `Z`?
(2) How to put a ring structure on `Z`?
(3) How to define a map from `Z` to Lean's `ℤ`, which
is not defined as a quotient but also satisfies the
universal property?

We will do (1) and (2) in this file. Let's start with (1).
The claim is that to give
a map `Z → T` is to give a map `N2 → T`
which is constant on equivalence classes. The
construction: given a map `Z → T`, just
compose with `quotient.mk : N2 → Z`.
What do we need to prove here?

First we need to prove that `quotient.mk` is `≈`-equivariant.
In other words, we need to prove `x ≈ y → ⟦x⟧ = ⟦y⟧`.

-/

example (x y : N2) : x ≈ y → ⟦x⟧ = ⟦y⟧ :=
quotient.sound

-- Of course we know the other implication is also true.
-- This is called `quotient.exact`.

example (x y : N2) : ⟦x⟧ = ⟦y⟧ → x ≈ y :=
quotient.exact

-- The iff statement (useful for rewrites) is called `quotient.eq` :

example (x y : N2) : ⟦x⟧ = ⟦y⟧ ↔ x ≈ y :=
quotient.eq

-- So now we can define the map from `Z → T` to the subtype of `N2 → T`
-- consisting of `≈`-equivariant functions.

variable {T : Type}

/- Given a map `g : Z → T`, make a function `f : N2 → T` which is
   constant on equivalence classes. -/
def universal1 (g : Z → T) :
  {f : N2 → T // ∀ x y : N2, x ≈ y → f x = f y} :=
⟨λ n2, g ⟦n2⟧, begin
  sorry
end⟩

-- To go the other way, we use a new function called `quotient.lift`.
-- Note that this is a weird name for the construction, at least if your
-- mental picture has the quotient underneath the type with the relation.
-- But we're stuck with it.

/- Given a map `f : N2 → T` plus the assumption that it is constant on
   equivalence classes, "lift" this map to a map `Z → T`. -/
def universal2 (f : N2 → T) (hf : ∀ x y : N2, x ≈ y → f x = f y) :
  Z → T :=
quotient.lift f hf

-- So now the big question is: how do we prove that these two constructions
-- are inverse to each other? In other words, what is the API for
-- the definition `quotient.lift`?
-- Let's start by showing that going from `N2 → T` to `Z → T` (via `quotient.lift`)
-- and then back to `N2 → T` (via composing with `quotient.mk`) is the
-- identity function. Recall `⟦⟧` is the notation for `quotient.mk`. 
-- Another way of writing the example below : universal2 ∘ universal1 = id.

example (f : N2 → T) (hf : ∀ x y : N2, x ≈ y → f x = f y) :
  f = λ n2, quotient.lift f hf ⟦n2⟧ :=
begin
  -- true by definition!
  refl
end

-- This is the reason quotients are defined as a black box; if we had
-- defined them to be equivalence classes this would be true, but
-- not by definition. To a mathematician this is not really a big deal,
-- but it is what it is.

-- To go the other way, proving universal1 ∘ universal2 = id, the key thing
-- to know is a function 
-- called `quotient.induction_on`:

example (g : Z → T) : g = quotient.lift (λ n2, g ⟦n2⟧) (universal1 g).2 :=
begin
  -- two functions are equal if they agree on all inputs
  ext z,
  -- now use `quotient.induction_on` (this is the key move)
  apply quotient.induction_on z,
  -- and now we're in the situation of the above example again
  intro ab,
  -- so it's true by definition.
  refl,
end

-- We have hence proved that `universal1` and `universal2` are inverse
-- bijections, at least in this `N2 → Z` case. In `Part_C` we will do
-- this in general, but there is a ton of material this week so
-- don't worry if you don't get to it.

/-

## Giving Z a commutative ring structure

Let's now show how to give this quotient object `Z` a commutative ring
structure, which it somehow wants to inherit from structures on `ℕ`. Recall
that a ring is a choice of `0`, `1`, and functions `+`, `-` and `*`
satisfying some axioms. After a while this all becomes straightforward
and boring, so I will go through the proof that it's an abelian group
under addition carefully and then the multiplication part is just more
of the same -- feel free to skip it.

### zero and one

We start by giving `Z` a zero and a one.

-/

def zero : Z := ⟦(0, 0)⟧

def one : Z := ⟦(1, 0)⟧

-- We don't have the numeral notation yet though:

-- #check (0 : Z) -- error about failing to find an instance of `has_zero Z`

-- Let's use numeral notation `0` and `1` for `zero` and `one`.

instance : has_zero Z := ⟨zero⟩
instance : has_one Z := ⟨one⟩

-- let's start to train the simplifier
@[simp] lemma zero_def : (0 : Z) = ⟦(0, 0)⟧ := rfl -- works 
@[simp] lemma one_def : (1 : Z) = ⟦(1, 0)⟧ := rfl

/-

### negation

Let's do negation next, by which I mean the function sending `z` to `-z`,
because this is a function which only takes one input (addition takes two).

Here is how a mathematician might describe defining negation on the
equivalence classes of `ℕ × ℕ`. They might say this:

1) choose an element `z` of the quotient `Z`.
2) lift it randomly to a pair `(a, b)` of natural numbers.
3) Define `-z` to be `⟦(b,a)⟧`
4) Now let us check that this definition did not depend on the random lift in (2):
   [and then they prove a lemma saying the construction is well-defined, i.e.
    that if `(a, b) ≈ (c,d)` then `⟦(b, a)⟧ = ⟦(d, c)⟧` ]

This is the way mathematicians are taught. We will use *the same
construction* in Lean but we will phrase it differently.

1') Define an auxiliary map `N2 → Z` by sending `(a,b)` to `⟦(b,a)⟧`
2') I claim that this function is constant on equivalence classes
    [and then we prove a lemma saying `(a, b) ≈ (c, d) → ⟦(b, a)⟧ = ⟦(d, c)⟧`
3') Now use `quotient.lift` to descend this to a map from `Z` to `Z`.

So as you can see, the mathematics is the same, but the emphasis is slightly
different. 
-/

-- Here's the auxiliary map.
def neg_aux (ab : N2) : Z := ⟦(ab.2, ab.1)⟧

-- useful for rewriting. Let's teach it to `simp`.
@[simp] lemma neg_aux_def (ab : N2) : neg_aux ab = ⟦(ab.2, ab.1)⟧ := rfl
  -- true by def

-- In the process of making this definition we need to prove a theorem
-- saying neg_aux is constant on equivalence classes.
def neg : Z → Z := quotient.lift neg_aux
begin
  -- ⊢ ∀ (a b : N2), a ≈ b → neg_aux a = neg_aux b
  sorry,
end

-- `-z` notation
instance : has_neg Z := ⟨neg⟩

-- Let's teach the definition of `neg` to the simplifier.
@[simp] lemma neg_def (a b : ℕ) : (-⟦(a, b)⟧ : Z) = ⟦(b, a)⟧ := rfl
/-

## Addition

If we use `quotient.lift` for defining addition, we'd have to use it twice.
We define `⟦(a, b)⟧ + ⟦(c, d)⟧ = ⟦(a + c, b + d)⟧` and would then have
to check it was independent of the choice of lift `(a, b)` in one lemma,
and then in a second proof check it was independent of the choice of `(c, d)`.
The variant `quotient.lift₂` enables us to prove both results in one go. 
It says that if `f : A → B → C` is a function which and `A` and `B`
have equivalence relations on them, and `f` is constant on equivalence
classes in both the `A` and the `B` variable, then `f` descends ("lifts")
to a function `A/~ → B/~ → C`.
-/

-- auxiliary definition of addition (note `(a-b)+(c-d)=(a+c)-(b+d)` )
def add_aux (ab cd : N2) : Z := ⟦(ab.1 + cd.1, ab.2 + cd.2)⟧

-- useful for rewriting
@[simp] lemma add_aux_def (ab cd : N2) :
  add_aux ab cd = ⟦(ab.1 + cd.1, ab.2 + cd.2)⟧ :=
rfl -- true by def

def add : Z → Z → Z := quotient.lift₂ add_aux 
begin
  sorry,
end

-- notation for addition
instance : has_add Z := ⟨add⟩

-- train the simplifier, because we have some axioms to prove about `+`
@[simp] lemma add_def (a b c d : ℕ) :
  (⟦(a, b)⟧ + ⟦(c, d)⟧ : Z) = ⟦(a+c, b+d)⟧ := 
rfl

-- may as well get subtraction working
def sub (x y : Z) : Z := x + -y

instance : has_sub Z := ⟨sub⟩

/-

## Z is a commutative group under addition

-/

def add_comm_group : add_comm_group Z :=
{ zero := 0,
  add := (+),
  neg := has_neg.neg, 
  sub := has_sub.sub,
  -- The key is always `quotient.induction_on`
  -- I'll do the first one for you.
  zero_add := begin
    intro x,
    apply quotient.induction_on x, clear x,
    rintro ⟨a, b⟩,
    simp,
  end,
  add_zero := begin
    sorry
  end,    
  -- Here there are three variables so it's `quotient.induction_on₃`
  -- Remember the `ring` tactic will prove identities in `ℕ`.
  add_assoc := begin
    sorry
  end,
  add_left_neg := begin
    sorry
  end,
  add_comm := begin
    sorry
  end,
}

/-

## More of the same : Z is a commutative ring.

I would recommend skipping this and going onto Part B.
There are no more ideas here, this is just to prove that it can be done.

A mild variant: let's do multiplication in a slightly different way.
Instead of using `quotient.lift₂` (which descends a map `N2 → N2 → Z` to a
map `Z → Z → Z`) we'll use `quotient.map₂`, which descends a
map `N2 → N2 → N2` to a map `Z → Z → Z`.

-/

-- auxiliary definition of multiplication: `(a-b)*(c-d) = (a*c+b*d)-(a*d+b*c)`
def mul_aux (ab cd : N2) : N2 :=
  (ab.1 * cd.1 + ab.2 * cd.2, ab.1 * cd.2 + ab.2 * cd.1)

@[simp] lemma mul_aux_def (a b c d : ℕ) :
  mul_aux (a,b) (c,d) = (a*c+b*d,a*d+b*c) := rfl

-- The key result you have to prove here involves multiplication so is
-- unfortunately non-linear. However `nlinarith` is OK at non-linear arithmetic...
def mul : Z → Z → Z := quotient.map₂ mul_aux 
begin
  sorry
end

-- notation for multiplication
instance : has_mul Z := ⟨mul⟩

@[simp] lemma mul_def (a b c d : ℕ) :
  (⟦(a, b)⟧ * ⟦(c, d)⟧ : Z) = ⟦(a*c+b*d, a*d+b*c)⟧ := rfl

-- now let's prove that Z is a commutative ring!

def comm_ring : comm_ring Z :=
{ one := 1,
  add := (+),
  mul := (*),
  mul_assoc := begin
    intros x y z,
    apply quotient.induction_on₃ x y z, clear x y z,
    rintros ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩,
    simp,
    ring,
  end,
  -- etc etc
  one_mul := begin
    sorry
  end,
  mul_one := begin
    sorry
  end,
  left_distrib := begin
    sorry
  end,
  right_distrib := begin
    sorry
  end,
  mul_comm := begin
    sorry
  end,
  ..add_comm_group
}

end Z
