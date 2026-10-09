import AllThoseEPPA.CycleSparseningSwitchAutomorphism

/-!
# Transport of cycle order under base automorphisms

Bad cycles are indexed ordered sequences, and transporting the vertices
does not change the displayed order.  In particular, the distinction
between ordinary consecutive edges and the closing edge is invariant.
-/

namespace AllThoseEPPA
namespace Structure
namespace BadCycleSequence

universe u v w

variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {act : L.Action Γ}
variable {A : Structure L V} {E : L.RelSymbol 2}

/-- Non-closing adjacency is invariant under transport of bad cycles. -/
theorem nonWrapPair_transport_iff
    (c : BadCycleSequence A E)
    (g : Automorphism act A)
    (hfix : act.FixesRel E)
    (x y : V) :
    (c.transport g hfix).NonWrapPair (g x) (g y) ↔
      c.NonWrapPair x y := by
  constructor
  · rintro ⟨i, j, hi, hj, hadj, hlin⟩
    refine ⟨i, j, ?_, ?_, hadj, hlin⟩
    · exact g.toEquiv.injective hi
    · exact g.toEquiv.injective hj
  · rintro ⟨i, j, hi, hj, hadj, hlin⟩
    refine ⟨i, j, ?_, ?_, hadj, hlin⟩
    · exact congrArg g hi
    · exact congrArg g hj

/-- Closing (wrap) adjacency is also invariant under transport. -/
theorem wrapPair_transport_iff
    (c : BadCycleSequence A E)
    (g : Automorphism act A)
    (hfix : act.FixesRel E)
    (x y : V) :
    (c.transport g hfix).WrapPair (g x) (g y) ↔
      c.WrapPair x y := by
  constructor
  · rintro ⟨i, j, hi, hj, hadj, hnlin⟩
    refine ⟨i, j, ?_, ?_, hadj, hnlin⟩
    · exact g.toEquiv.injective hi
    · exact g.toEquiv.injective hj
  · rintro ⟨i, j, hi, hj, hadj, hnlin⟩
    refine ⟨i, j, ?_, ?_, hadj, hnlin⟩
    · exact congrArg g hi
    · exact congrArg g hj

end BadCycleSequence
end Structure
namespace Sparsening

universe u v w

variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w}
variable (act : L.Action Γ) (A : Structure L V) (E : L.RelSymbol 2)

/-- Base automorphisms reindex valuation functions by their induced
permutation of the bad cycle sequences, without changing Boolean values. -/
noncomputable def valuationFunctionTransportEquiv
    (g : Structure.Automorphism act A)
    (hfix : act.FixesRel E) (x : V) :
    ValuationFunction A E x ≃ ValuationFunction A E (g x) :=
  Equiv.piCongr
    (W := fun _ : BadCyclesAt A E x => Bool)
    (Z := fun _ : BadCyclesAt A E (g x) => Bool)
    (badCyclesAtEquiv act A E g hfix x)
    (fun _ => Equiv.refl Bool)

theorem valuationFunctionTransportEquiv_apply_transport
    (g : Structure.Automorphism act A)
    (hfix : act.FixesRel E) (x : V)
    (χ : ValuationFunction A E x)
    (I : BadCyclesAt A E x) :
    valuationFunctionTransportEquiv act A E g hfix x χ
        (badCyclesAtEquiv act A E g hfix x I) = χ I := by
  exact Equiv.piCongr_apply_apply
    (W := fun _ : BadCyclesAt A E x => Bool)
    (Z := fun _ : BadCyclesAt A E (g x) => Bool)
    (badCyclesAtEquiv act A E g hfix x)
    (fun _ => Equiv.refl Bool) χ I

/-- Lift the base automorphism to valuation points, before introducing flips. -/
noncomputable def valuationPointTransport
    (g : Structure.Automorphism act A)
    (hfix : act.FixesRel E)
    (p : ValuationPoint A E) : ValuationPoint A E :=
  Sigma.map g
    (fun x => valuationFunctionTransportEquiv act A E g hfix x) p

@[simp] theorem valuationPointTransport_base
    (g : Structure.Automorphism act A)
    (hfix : act.FixesRel E)
    (p : ValuationPoint A E) :
    (valuationPointTransport act A E g hfix p).1 = g p.1 :=
  rfl

theorem valuationPointTransport_injective
    (g : Structure.Automorphism act A)
    (hfix : act.FixesRel E) :
    Function.Injective (valuationPointTransport act A E g hfix) :=
  g.toEquiv.injective.sigma_map
    (fun x => (valuationFunctionTransportEquiv act A E g hfix x).injective)

end Sparsening

end AllThoseEPPA
