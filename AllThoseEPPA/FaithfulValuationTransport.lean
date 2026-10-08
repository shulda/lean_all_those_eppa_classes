import AllThoseEPPA.FaithfulLabelExtension
import AllThoseEPPA.FaithfulClosureTransport

/-!
# Transport of faithful valuation functions

The family of total label extensions attached to a compatible base
automorphism induces a genuine equivalence between valuation-function spaces.
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

/-- Fibre equivalence over a target bad irreducible, obtained by transporting
back to the source bad irreducible, applying the canonical label extension,
and then casting along the round-trip equality. -/
noncomputable def valuationLabelFibreEquiv [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (x : β)
    (J : BadAt act A B₀ ψ (g x)) :
    BadLabel act A B₀ ψ
        (((badAtEquiv act A B₀ ψ g x).symm J).1) ≃
      BadLabel act A B₀ ψ J.1 := by
  let I : BadAt act A B₀ ψ x :=
    (badAtEquiv act A B₀ ψ g x).symm J
  have hIJ :
      I.1.transport act A B₀ ψ g = J.1 := by
    exact congrArg Subtype.val
      ((badAtEquiv act A B₀ ψ g x).apply_symm_apply J)
  exact
    (labelExtension act A B₀ ψ p g I.1
      hsource htarget hcompat).trans
      (badLabelEquivOfEq act A B₀ ψ hIJ)

/-- Transport of an entire valuation function along a compatible base
automorphism.  This is a dependent product of the corresponding label
extensions. -/
noncomputable def valuationFunctionEquiv [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (x : β) :
    ValuationFunction act A B₀ ψ x ≃
      ValuationFunction act A B₀ ψ (g x) :=
  (badAtEquiv act A B₀ ψ g x).piCongr'
    (fun J =>
      valuationLabelFibreEquiv act A B₀ ψ
        p g hsource htarget hcompat x J)

/-- Evaluation of transported valuation functions at a transported bad
irreducible is the corresponding total label extension. -/
theorem valuationFunctionEquiv_apply_transport [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (x : β)
    (χ : ValuationFunction act A B₀ ψ x)
    (I : BadAt act A B₀ ψ x) :
    valuationFunctionEquiv act A B₀ ψ
        p g hsource htarget hcompat x χ
        (badAtEquiv act A B₀ ψ g x I) =
      labelExtension act A B₀ ψ p g I.1
        hsource htarget hcompat (χ I) := by
  simp only [valuationFunctionEquiv, Equiv.piCongr'_apply]
  apply Subtype.ext
  let e := badAtEquiv act A B₀ ψ g x
  let I' : BadAt act A B₀ ψ x := e.symm (e I)
  have hround : I' = I := by
    exact e.symm_apply_apply I
  change
    ((valuationLabelFibreEquiv act A B₀ ψ
        p g hsource htarget hcompat x (e I))
      (χ I')).1 =
      ((labelExtension act A B₀ ψ p g I.1
        hsource htarget hcompat) (χ I)).1
  calc
    ((valuationLabelFibreEquiv act A B₀ ψ
        p g hsource htarget hcompat x (e I))
      (χ I')).1 =
        ((labelExtension act A B₀ ψ p g I'.1
          hsource htarget hcompat) (χ I')).1 := by
      simp [valuationLabelFibreEquiv, e, I']
    _ =
        ((labelExtension act A B₀ ψ p g I.1
          hsource htarget hcompat) (χ I)).1 := by
      exact congrArg
        (fun K : BadAt act A B₀ ψ x =>
          ((labelExtension act A B₀ ψ p g K.1
            hsource htarget hcompat) (χ K)).1)
        hround

end Faithful
end AllThoseEPPA
