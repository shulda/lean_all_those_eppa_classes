import AllThoseEPPA.FaithfulWitnessCoherence
import AllThoseEPPA.FaithfulCanonicalCoherence

/-!
# Coherent EPPA for the irreducible-structure faithful witness
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

/-- The canonical faithful lift of the base extension selected for a partial
automorphism of the original structure. -/
noncomputable def faithfulLiftAutomorphism [Finite β]
    (E : Structure.CoherentExtension act ψ)
    (p : Structure.PartialAutomorphism act A) :
    Structure.Automorphism act
      (witnessStructure act A B₀ ψ) :=
  faithfulWitnessAutomorphism act A B₀ ψ
    (canonicalPartialAutomorphism act A B₀ ψ p)
    (E.extension p)
    (canonicalPartialAutomorphism_source_generic
      act A B₀ ψ p)
    (canonicalPartialAutomorphism_target_generic
      act A B₀ ψ p)
    (canonicalPartialAutomorphism_baseCompatible
      act A B₀ ψ p (E.extension p)
      (E.extension_spec p))

/-- The canonical faithful lift really extends the original partial
automorphism along the canonical embedding. -/
theorem faithfulLiftAutomorphism_extends [Finite β]
    (E : Structure.CoherentExtension act ψ)
    (p : Structure.PartialAutomorphism act A) :
    Structure.ExtendsAlong act
      (canonicalEmbedding act A B₀ ψ)
      p
      (faithfulLiftAutomorphism act A B₀ ψ E p) := by
  constructor
  · change (E.extension p).lang * ψ.lang =
      ψ.lang * p.lang
    exact (E.extension_spec p).1
  · intro a ha
    let P :=
      canonicalPartialAutomorphism act A B₀ ψ p
    have hsrc :
        canonicalVertex act A B₀ ψ a ∈ P.source := by
      simpa [P, canonicalPartialAutomorphism] using
        (canonicalVertex_mem_partialSource
          act A B₀ ψ p a ha)
    change
      WitnessVertex.transport act A B₀ ψ
          P (E.extension p)
          (canonicalPartialAutomorphism_source_generic
            act A B₀ ψ p)
          (canonicalPartialAutomorphism_target_generic
            act A B₀ ψ p)
          (canonicalPartialAutomorphism_baseCompatible
            act A B₀ ψ p (E.extension p)
            (E.extension_spec p))
          (canonicalVertex act A B₀ ψ a) =
        canonicalVertex act A B₀ ψ (p a)
    calc
      WitnessVertex.transport act A B₀ ψ
          P (E.extension p)
          (canonicalPartialAutomorphism_source_generic
            act A B₀ ψ p)
          (canonicalPartialAutomorphism_target_generic
            act A B₀ ψ p)
          (canonicalPartialAutomorphism_baseCompatible
            act A B₀ ψ p (E.extension p)
            (E.extension_spec p))
          (canonicalVertex act A B₀ ψ a) =
        P (canonicalVertex act A B₀ ψ a) := by
          exact
            WitnessVertex.transport_eq_of_mem_source
              act A B₀ ψ P (E.extension p)
              (canonicalPartialAutomorphism_source_generic
                act A B₀ ψ p)
              (canonicalPartialAutomorphism_target_generic
                act A B₀ ψ p)
              (canonicalPartialAutomorphism_baseCompatible
                act A B₀ ψ p (E.extension p)
                (E.extension_spec p))
              (canonicalVertex act A B₀ ψ a) hsrc
      _ = canonicalVertex act A B₀ ψ (p a) := by
        simpa [P] using
          (canonicalPartialAutomorphism_apply
            act A B₀ ψ p a ha)

end Faithful
end AllThoseEPPA
