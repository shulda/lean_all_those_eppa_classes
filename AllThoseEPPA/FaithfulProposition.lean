import AllThoseEPPA.FaithfulCoherence
import AllThoseEPPA.FaithfulFaithfulness
import AllThoseEPPA.FaithfulIrreducible

/-!
# Proposition `prop:faithful`

This file packages the faithful-witness construction into the statement used
in the paper.
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

/-- **Proposition `prop:faithful`.**  Over a finite EPPA witness `B₀`,
the explicit faithful construction has finite carrier, is an EPPA witness for
the canonical copy of `A`, is irreducible-structure faithful, and projects
to `B₀` by a homomorphism-embedding.  If the chosen base witness is coherent,
the faithful witness is coherent as well. -/
theorem faithfulWitness_proposition [Finite β]
    (hB₀ : Structure.IsEPPAWitness act ψ) :
    Finite (WitnessVertex act A B₀ ψ) ∧
    Structure.IsEPPAWitness act
      (canonicalEmbedding act A B₀ ψ) ∧
    Structure.IsIrreducibleStructureFaithful act
      (canonicalEmbedding act A B₀ ψ) ∧
    Structure.Homomorphism.IsHomomorphismEmbedding act
      (projection act A B₀ ψ) ∧
    (Structure.IsCoherentEPPAWitness act ψ →
      Structure.IsCoherentEPPAWitness act
        (canonicalEmbedding act A B₀ ψ)) := by
  refine ⟨witnessVertex_finite act A B₀ ψ, ?_⟩
  refine
    ⟨faithfulWitness_isEPPAWitness
      act A B₀ ψ hB₀, ?_⟩
  refine
    ⟨faithfulWitness_isIrreducibleStructureFaithful
      act A B₀ ψ, ?_⟩
  refine
    ⟨projection_isHomomorphismEmbedding
      act A B₀ ψ, ?_⟩
  intro hcoh
  exact
    faithfulWitness_isCoherentEPPAWitness
      act A B₀ ψ hcoh

end Faithful
end AllThoseEPPA
