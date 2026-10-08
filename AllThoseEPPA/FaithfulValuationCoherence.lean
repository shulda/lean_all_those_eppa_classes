import AllThoseEPPA.FaithfulLabelCoherence

/-!
# Coherence of faithful valuation transport
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)

/-- Transport of a bad-at index along a composite base automorphism agrees
with successive transport. -/
theorem badAtEquiv_comp
    (gp gq : Structure.Automorphism act B₀)
    (x : β)
    (I : BadAt act A B₀ ψ x) :
    badAtEquiv act A B₀ ψ (gq.comp gp) x I =
      badAtEquiv act A B₀ ψ gq (gp x)
        (badAtEquiv act A B₀ ψ gp x I) := by
  apply Subtype.ext
  exact
    (BadIrreducible.transport_comp
      act A B₀ ψ gq gp I.1).symm

end Faithful
end AllThoseEPPA
