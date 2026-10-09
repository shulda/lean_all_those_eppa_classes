import AllThoseEPPA.Irreducible
import AllThoseEPPA.Automorphism

/-!
# Basic graph infrastructure for the sparsening construction

Section `sec:cycles` of the paper singles out a binary relation symbol `E`
which is fixed by the language action and is interpreted as a simple graph.
This file provides the small amount of graph vocabulary needed for the
formalization of Lemma `lem:sparsen`, without changing the ambient notion of
a Γ_L-structure.
-/

namespace AllThoseEPPA

universe u v w

namespace Language
namespace Action

variable {L : Language.{u}} {Γ : Type v} [Group Γ]

/-- A relation symbol is fixed by the language action. -/
def FixesRel
    (act : L.Action Γ) {n : ℕ} (R : L.RelSymbol n) : Prop :=
  ∀ g : Γ, act.onRel g R = R

end Action
end Language

namespace Structure

variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w}
variable {act : L.Action Γ}

/-- The ordered two-tuple with entries `x,y`. -/
def pairTuple (x y : V) : Fin 2 → V :=
  fun i => if i = 0 then x else y

@[simp] theorem pairTuple_zero (x y : V) :
    pairTuple x y 0 = x := by
  simp [pairTuple]

@[simp] theorem pairTuple_one (x y : V) :
    pairTuple x y 1 = y := by
  simp [pairTuple]

/-- Mapping a two-tuple pointwise gives the corresponding two-tuple. -/
theorem pairTuple_map {W : Type*} (f : V → W) (x y : V) :
    f ∘ pairTuple x y = pairTuple (f x) (f y) := by
  funext i
  by_cases hi : i = 0 <;> simp [pairTuple, hi]

/-- The edge predicate associated with a distinguished binary relation. -/
def Edge (A : Structure L V) (E : L.RelSymbol 2) (x y : V) : Prop :=
  A.rel E (pairTuple x y)

/-- The distinguished relation is loopless. -/
def EdgeLoopless (A : Structure L V) (E : L.RelSymbol 2) : Prop :=
  ∀ x : V, ¬ A.Edge E x x

/-- The distinguished relation is symmetric. -/
def EdgeSymmetric (A : Structure L V) (E : L.RelSymbol 2) : Prop :=
  ∀ x y : V, A.Edge E x y ↔ A.Edge E y x

/-- The distinguished relation is the complete simple graph. -/
def EdgeComplete (A : Structure L V) (E : L.RelSymbol 2) : Prop :=
  ∀ x y : V, A.Edge E x y ↔ x ≠ y

theorem EdgeComplete.loopless
    {A : Structure L V} {E : L.RelSymbol 2}
    (h : A.EdgeComplete E) :
    A.EdgeLoopless E := by
  intro x hx
  exact (h x x).mp hx rfl

theorem EdgeComplete.symmetric
    {A : Structure L V} {E : L.RelSymbol 2}
    (h : A.EdgeComplete E) :
    A.EdgeSymmetric E := by
  intro x y
  rw [h x y, h y x]
  exact ne_comm

namespace Automorphism

/-- A total automorphism preserves a distinguished relation which is fixed by
the language action. -/
theorem edge_map_iff
    {A : Structure L V}
    (g : Automorphism act A)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (x y : V) :
    A.Edge E (g x) (g y) ↔ A.Edge E x y := by
  have h :=
    g.map_rel_iff E (pairTuple x y)
  rw [hfix g.lang] at h
  rw [pairTuple_map] at h
  exact h

end Automorphism

namespace Embedding

variable {W : Type*} {A : Structure L V} {B : Structure L W}

/-- An embedding preserves and reflects a distinguished relation fixed by the
language action. -/
theorem edge_map_iff
    (f : Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (x y : V) :
    B.Edge E (f x) (f y) ↔ A.Edge E x y := by
  have h :=
    f.map_rel_iff E (pairTuple x y)
  rw [hfix f.lang] at h
  rw [pairTuple_map] at h
  exact h

end Embedding

/-- The successor relation on the cyclically ordered index set `Fin k`. -/
def CyclicSuccessor {k : ℕ} (i j : Fin k) : Prop :=
  j.1 = (i.1 + 1) % k

/-- Two indices are adjacent on the unoriented `k`-cycle. -/
def CyclicAdjacent {k : ℕ} (i j : Fin k) : Prop :=
  CyclicSuccessor i j ∨ CyclicSuccessor j i

theorem cyclicAdjacent_symm {k : ℕ} (i j : Fin k) :
    CyclicAdjacent i j ↔ CyclicAdjacent j i := by
  constructor <;> intro h
  · rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- A bad cycle sequence from Section `sec:cycles`: an ordered sequence of
at least four distinct vertices on which `E` induces exactly the cycle in
that cyclic order. -/
structure BadCycleSequence
    (A : Structure L V) (E : L.RelSymbol 2) where
  length : ℕ
  length_ge_four : 4 ≤ length
  vertex : Fin length → V
  injective : Function.Injective vertex
  edge_iff :
    ∀ i j : Fin length,
      A.Edge E (vertex i) (vertex j) ↔ CyclicAdjacent i j

namespace BadCycleSequence

variable {A : Structure L V} {E : L.RelSymbol 2}

/-- The set of vertices occurring in a bad cycle sequence. -/
def carrier (c : BadCycleSequence A E) : Set V :=
  Set.range c.vertex

theorem mem_carrier_iff (c : BadCycleSequence A E) (x : V) :
    x ∈ c.carrier ↔ ∃ i, c.vertex i = x :=
  Iff.rfl

/-- Automorphisms transport bad cycle sequences when the distinguished
relation is fixed by the language action. -/
noncomputable def transport
    (c : BadCycleSequence A E)
    (g : Automorphism act A)
    (hfix : act.FixesRel E) :
    BadCycleSequence A E where
  length := c.length
  length_ge_four := c.length_ge_four
  vertex := g ∘ c.vertex
  injective := g.toEquiv.injective.comp c.injective
  edge_iff := by
    intro i j
    exact
      (Automorphism.edge_map_iff
        g E hfix (c.vertex i) (c.vertex j)).trans
        (c.edge_iff i j)

@[simp] theorem transport_length
    (c : BadCycleSequence A E)
    (g : Automorphism act A)
    (hfix : act.FixesRel E) :
    (c.transport g hfix).length = c.length :=
  rfl

@[simp] theorem transport_vertex
    (c : BadCycleSequence A E)
    (g : Automorphism act A)
    (hfix : act.FixesRel E)
    (i : Fin c.length) :
    (c.transport g hfix).vertex i = g (c.vertex i) :=
  rfl

end BadCycleSequence

end Structure
end AllThoseEPPA
