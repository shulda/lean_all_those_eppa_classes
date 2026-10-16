import AllThoseEPPA.Applications.KOrientations.FirstStageInClass
import AllThoseEPPA.EPPA

/-!
# First-stage EPPA automorphisms transport their actual closed domains exactly

An auxiliary-root partial isomorphism between original d-closed source
and target sets needs one first-stage automorphism g whose image of the
ENTIRE old closed source domain equals the ENTIRE old closed target
domain. Mere pointwise extension on source vertices cannot be used as
a substitute unless surjectivity on the partial range is proved.

The checked public EPPA API supplies exactly these ingredients:
a partial isomorphism's PartialEquiv is bijective between its source
and target; an ExtendsAlong witness guarantees the automorphism square
on the original embedded source domain. Consequently
  g '' (ψ '' p.source) = ψ '' p.target
as literal sets in the first-stage witness.

No finite-language, bounded-orientation, or old-domain-invariance
assumption is added. This source-independent lemma is precisely the
set-image gate later used by the root-domain Γ-partial-isomorphism
constructor; it also applies to any other EPPA construction.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w z

variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type z}

/-- Every genuine extension of a partial automorphism along an
embedding maps the ENTIRE embedded partial SOURCE exactly ONTO its
embedded TARGET, not just into it.

The reverse inclusion uses the inverse-on-target property of the
actual PartialEquiv; no cardinality argument or arbitrary choice of
domain representatives is needed. -/
theorem extendsAlong_image_source_eq_target
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (ψ : Embedding act A B)
    (p : PartialAutomorphism act A)
    (g : Automorphism act B)
    (hExt : ExtendsAlong act ψ p g) :
    g '' (ψ.toFun '' p.source) = ψ.toFun '' p.target := by
  ext y
  constructor
  · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨p x, p.map_source hx, ?_⟩
    exact (hExt.2 x hx).symm
  · rintro ⟨x, hx, rfl⟩
    let z : V := p.toPartialEquiv.symm x
    have hz : z ∈ p.source := p.toPartialEquiv.map_target hx
    have hzx : p z = x := p.right_inv hx
    refine ⟨ψ z, ⟨z, hz, rfl⟩, ?_⟩
    calc
      g (ψ z) = ψ (p z) := hExt.2 z hz
      _ = ψ x := congrArg ψ.toFun hzx

end Structure
end AllThoseEPPA
