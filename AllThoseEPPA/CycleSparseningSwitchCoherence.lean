import AllThoseEPPA.CycleSparseningSwitchAlgebra
import AllThoseEPPA.CycleSparseningSwitchAutomorphism

/-!
# Coherent composition of simultaneous Boolean cycle switches

This theorem isolates the F₂-valued group law of the flip part of the
sparsening extension. It is a direct ingredient in coherent EPPA.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Composition of two global switch automorphisms is the global switch
whose bit at each indexed bad cycle is the XOR of the two original bits. -/
theorem witnessFlipAutomorphism_comp
    (s t : Structure.BadCycleSequence B₀ E → Bool) :
    (witnessFlipAutomorphism B₀ E s act).comp
      (witnessFlipAutomorphism B₀ E t act) =
    witnessFlipAutomorphism B₀ E (switchSum B₀ E s t) act := by
  apply Structure.Automorphism.ext_of_lang_apply
  · simp
  · intro w
    change
      (w.flip B₀ E t).flip B₀ E s =
      w.flip B₀ E (switchSum B₀ E s t)
    exact WitnessVertex.flip_comp B₀ E s t w

end Sparsening
end AllThoseEPPA
