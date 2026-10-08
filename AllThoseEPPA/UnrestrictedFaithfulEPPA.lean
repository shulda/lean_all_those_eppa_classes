import AllThoseEPPA.FaithfulProposition
import AllThoseEPPA.UnaryFunctionsCoherence

/-!
# The unrestricted irreducible-structure faithful coherent EPPA theorem
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v} [Fintype α]
variable (act : L.Action Γ) (A : Structure L α)

/-- **Theorem `thm:nreppa` (construction of an unrestricted EPPA
witness).**  A finite structure in a finite relabelling orbit has a finite
irreducible-structure faithful coherent EPPA witness. -/
theorem finiteOrbitUnaryStructuresHaveFaithfulCoherentEPPA
    (hA : A.HasFiniteRelabelOrbit act) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
        (B : Structure L δ)
        (ι : Structure.Embedding act A B),
      Structure.IsCoherentEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι := by
  rcases
      UnaryFunctions.finiteOrbitUnaryStructuresHaveCoherentEPPA
        act A hA with
    ⟨δ, hδ, B₀, ψ, hcoh⟩
  letI : Finite δ := hδ
  let W := WitnessVertex act A B₀ ψ
  have hW : Finite W :=
    witnessVertex_finite act A B₀ ψ
  refine
    ⟨W, hW,
      witnessStructure act A B₀ ψ,
      canonicalEmbedding act A B₀ ψ,
      ?_, ?_⟩
  · exact
      faithfulWitness_isCoherentEPPAWitness
        act A B₀ ψ hcoh
  · exact
      faithfulWitness_isIrreducibleStructureFaithful
        act A B₀ ψ

end Faithful
end AllThoseEPPA
