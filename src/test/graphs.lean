import data.multiset
import data.finset
import data.nat.basic
import tactic


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

namespace Graph 

variable {V : Type u}
variables (G : Graph V) --(v : V)

def nhbd (v : V) : set V := set_of (G.adj v)
--  {w : V | G.adj v w}

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

end Graph

