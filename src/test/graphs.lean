import data.fintype.basic
import data.finset
import data.nat.basic
import category_theory.category

import algebra.big_operators.basic
import tactic

open_locale big_operators -- enable notation


/-
Type for oriented simple graph with loops
-/
structure OrGraph :=
(V : Type)
[hfinite : finset V]
(E : set (V × V))

/-
Type or non-oriented simple graph
-/
universe u


@[ext]
structure Graph (V : Type u) :=
(adj : V → V → Prop)
(sym : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)

@[ext]
structure Grph :=
{V : Type u} 
(adj : V → V → Prop)
(sym : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)

namespace Graph 

variable {V : Type u}
variables (G : Graph V) 

def nhbd (v : V) : set V := set_of (G.adj v)


@[simp] 
lemma nhbd_def (v : V) : nhbd G (v : V) = {w : V | G.adj v w} := rfl

def OneVertex : Graph (fin 1) :=
⟨ (λ _ _, false), 
  (by {unfold symmetric, tauto}), 
  (by {intro, simp only [not_false_iff],}) ⟩ 

def degree (v : V) [fintype (G.nhbd v)] : ℕ := (G.nhbd v).to_finset.card

@[simp]
lemma degree_def (v : V) [fintype (G.nhbd v)] : G.degree (v : V) = (G.nhbd v).to_finset.card := rfl

lemma onevertexZeroDegree : OneVertex.degree (0 : fin 1) = 0 :=
begin 
  have : (OneVertex.nhbd 0) = ∅, by refl,
  unfold degree, 
  rw this,
  simp only [set.to_finset_card, set.empty_card'],
end 

--section morphism
universes u₁ u₂
variables {W : Type u₁} {U : Type u₂}
variables (H : Graph W) (K : Graph U)

@[ext]
structure Graph.map (G : Graph V) (H : Graph W) := 
(φ : V → W)
(Hadj : ∀ v w, G.adj v w → H.adj (φ v) (φ w) )

def Graph.id : Graph.map (G : Graph V) (G : Graph V) := 
⟨id, 
begin 
  intros v w h,
  dsimp,
  exact h
end ⟩

def Graph.comp (g : Graph.map H K) (f : Graph.map G H ) : Graph.map G K := 
{ φ := g.φ ∘ f.φ,
  Hadj := 
  begin 
    intros v w h,
    apply g.2,
    apply f.2,
    exact h,
  end 
}


end Graph 

namespace Grph
universes u₁
--variables {V : Type u} {W : Type u₁}
variables (G : Grph) (H : Grph) (K : Grph) 

def Grph.V (G : Grph) := G.1 

@[ext]
structure map (G : Grph) (H : Grph) := 
(φ : G.V → H.V)
(Hadj : ∀ v w, G.adj v w → H.adj (φ v) (φ w) )

def comp {G H K : Grph} (f : Grph.map G H ) (g : Grph.map H K) : Grph.map G K := 
{ φ := g.φ ∘ f.φ,
  Hadj := 
  begin 
    intros v w h,
    apply g.2,
    apply f.2,
    exact h,
  end 
}

def id : Grph.map (G : Grph) (G : Grph) := 
⟨id, 
begin 
  intros v w h,
  dsimp,
  exact h,
end ⟩

instance : category_theory.category (Grph) := 
{ hom := Grph.map,
  id := Grph.id,
  comp := λ G H K f g, Grph.comp f g,
  id_comp' := 
    begin 
      intros X Y f,
      cases f,
      simp,
      unfold Grph.comp,
      simp,
      unfold Grph.id,
      simp,
    end,
  comp_id' := 
    begin 
      intros X Y f,
      cases f,
      simp,
      unfold Grph.comp,
      simp,
      unfold Grph.id,
      simp,
    end ,
  assoc' := 
    begin
      intros,
      simp,
      unfold Grph.comp,
    end  
}

def nhbd (v : G.V) : set G.V := set_of (G.adj v)

@[simp] 
lemma nhbd_def (v : G.V) : nhbd G (v : G.V) = {w : G.V | G.adj v w} := rfl

def OneVertex : Grph :=
⟨  (λ (v : fin 1) _, false), 
  (by {unfold symmetric, tauto}), 
  (by {intro, simp only [not_false_iff],}) ⟩ 

def degree (v : G.V) [fintype (G.nhbd v)] : ℕ := (G.nhbd v).to_finset.card

@[simp]
lemma degree_def (v : G.V) [fintype (G.nhbd v)] : G.degree (v : G.V) = (G.nhbd v).to_finset.card := rfl

noncomputable instance (G : Grph) {h : fintype G.V} (v : G.V) : fintype (G.nhbd v) := 
by { simp, classical, apply set_fintype,}

instance : fintype OneVertex.V :=
{ elems := by {fsplit, exact ( (0 : fin 1) ::ₘ multiset.zero), exact dec_trivial,},
  complete := by {intro x, left, cases x, ext1, have : x_val = 0, by linarith, assumption,} }

lemma onevertexZeroDegree : OneVertex.degree (0 : fin 1) = 0 :=
begin 
  intros,
  have : (OneVertex.nhbd (0 : fin 1)) = ∅, by refl,
  unfold degree, 
  rw this,
  simp only [set.to_finset_card, set.empty_card'],
end 


end Grph

---------------------------------------------------------------
-- handshake lemma

open Grph 
variables (G : Grph) {hfin : fintype G.V}

#check hfin.1.sum 

def darts : set (G.V × G.V) := { e | ∃(x y : G.V), e = (x, y) ∧ G.adj x y}

def source {G : Grph} (a : darts G) : G.V := a.1.1

@[simp] lemma source_def {G : Grph} ( d : darts G) : source d = d.1.1 := rfl

variables (a : darts G) (b : darts G)

instance by_sources : (setoid (darts G)) :=
{ r := λ a b, source a = source b,
  iseqv := 
  begin 
    tidy,
  end 
}

@[simp] 
lemma eq_def : a ≈ b ↔ source a = source b :=
begin
  simp,
  split,
  {
    intro h,
    assumption,
  },
  {
    intro h,
    assumption
  }
end 

noncomputable instance : decidable_rel (by_sources G).r := 
begin 
  intros a b, 
  have : setoid.r a b = (a ≈ b), by refl,
  rw this,
  rw eq_def,
  cases b, cases a, cases a_val, cases b_val, dsimp at *,
  exact classical.dec (a_val_fst = b_val_fst),
end

#check by_sources 
#check finset.sum_partition (by_sources G) 

lemma darts_fintype {hfin : fintype G.V} : fintype (darts G) :=
begin
  fsplit,
  
end 


lemma sum_degrees_darts : hfin.1.sum (λ v, G.degree v) = (darts G).to_finset.card :=
begin 
  tidy,
  sorry,
end 
lemma sum_degrees_even : hfin.1.sum (λ v, G.degree v) % 2 = 0 :=
begin 
  tidy,
  sorry,
end 

---------------------------------------------------------------

