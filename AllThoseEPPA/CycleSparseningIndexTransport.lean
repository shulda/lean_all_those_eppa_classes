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
end AllThoseEPPA
