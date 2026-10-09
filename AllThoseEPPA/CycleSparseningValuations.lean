import AllThoseEPPA.CycleSparseningFaithfulEdge

/-!
# Cycle valuations for the sparsening construction

This file introduces the sets `U(x)` of bad induced cycle sequences through a
vertex and the binary valuation functions used in Section `sec:cycles`.
It also packages transport of bad cycles by base automorphisms as genuine
equivalences.
-/

namespace AllThoseEPPA

universe u v w

namespace Structure
namespace BadCycleSequence

variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w}
variable {act : L.Action Γ}
variable {A : Structure L V} {E : L.RelSymbol 2}

/-- Equality of bad cycle sequences is determined by their length and ordered
vertex sequence; all remaining fields are propositions. -/
theorem ext_vertex
    (c d : BadCycleSequence A E)
    (hlen : c.length = d.length)
    (hvertex : HEq c.vertex d.vertex) :
    c = d := by
  cases c with
  | mk k hk cv ci ce =>
    cases d with
    | mk l hl dv di de =>
      dsimp at hlen hvertex
      cases hlen
      have hv : cv = dv := eq_of_heq hvertex
      cases hv
      rfl

/-- Transporting by an automorphism and then its inverse recovers the cycle. -/
@[simp] theorem transport_symm_transport
    (c : BadCycleSequence A E)
    (g : Automorphism act A)
    (hfix : act.FixesRel E) :
    (c.transport g hfix).transport g.symm hfix = c := by
  apply
    ext_vertex
      ((c.transport g hfix).transport g.symm hfix)
      c rfl
  apply heq_of_eq
  funext i
  simp [transport, Function.comp_apply]

/-- Transporting by the inverse and then the automorphism recovers the cycle. -/
@[simp] theorem transport_transport_symm
    (c : BadCycleSequence A E)
    (g : Automorphism act A)
    (hfix : act.FixesRel E) :
    (c.transport g.symm hfix).transport g hfix = c := by
  apply
    ext_vertex
      ((c.transport g.symm hfix).transport g hfix)
      c rfl
  apply heq_of_eq
  funext i
  simp [transport, Function.comp_apply]

/-- Base automorphisms permute the bad cycle sequences. -/
noncomputable def transportEquiv
    (g : Automorphism act A)
    (hfix : act.FixesRel E) :
    BadCycleSequence A E ≃ BadCycleSequence A E where
  toFun := fun c => c.transport g hfix
  invFun := fun c => c.transport g.symm hfix
  left_inv := fun c => transport_symm_transport c g hfix
  right_inv := fun c => transport_transport_symm c g hfix

/-- Membership in the carrier of a transported bad cycle is transported
exactly by the base automorphism. -/
theorem mem_transport_carrier_iff
    (c : BadCycleSequence A E)
    (g : Automorphism act A)
    (hfix : act.FixesRel E)
    (x : V) :
    g x ∈ (c.transport g hfix).carrier ↔ x ∈ c.carrier := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change g (c.vertex i) = g x at hi
    exact g.toEquiv.injective hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change g (c.vertex i) = g x
    exact congrArg g hi

end BadCycleSequence
end Structure

namespace Sparsening

variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w}
variable (act : L.Action Γ)
variable (A : Structure L V)
variable (E : L.RelSymbol 2)

/-- Bad cycle sequences containing a fixed base vertex: the paper's `U(x)`. -/
abbrev BadCyclesAt (x : V) :=
  {c : Structure.BadCycleSequence A E // x ∈ c.carrier}

/-- Automorphisms transport `U(x)` bijectively onto `U(gx)`. -/
noncomputable def badCyclesAtEquiv
    (g : Structure.Automorphism act A)
    (hfix : act.FixesRel E)
    (x : V) :
    BadCyclesAt A E x ≃ BadCyclesAt A E (g x) where
  toFun := fun c =>
    ⟨c.1.transport g hfix,
      (Structure.BadCycleSequence.mem_transport_carrier_iff
        c.1 g hfix x).2 c.2⟩
  invFun := fun c =>
    ⟨c.1.transport g.symm hfix,
      by
        have h :=
          (Structure.BadCycleSequence.mem_transport_carrier_iff
            c.1 g.symm hfix (g x)).2 c.2
        simpa using h⟩
  left_inv := by
    intro c
    apply Subtype.ext
    exact
      Structure.BadCycleSequence.transport_symm_transport
        c.1 g hfix
  right_inv := by
    intro c
    apply Subtype.ext
    exact
      Structure.BadCycleSequence.transport_transport_symm
        c.1 g hfix

/-- A binary valuation function for a vertex in the cycle-sparsening
construction. -/
abbrev ValuationFunction (x : V) :=
  BadCyclesAt A E x → Bool

/-- A base point together with a cycle valuation. -/
abbrev ValuationPoint :=
  Σ x : V, ValuationFunction A E x

end Sparsening
end AllThoseEPPA
