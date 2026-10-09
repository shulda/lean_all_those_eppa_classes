import AllThoseEPPA.CycleSparseningCoherence
import AllThoseEPPA.CycleSparseningIrreducibleFaithfulness

/-!
# The complete induced-cycle sparsening lemma

All assertions of Section `lem:sparsen` are collected here, with an
explicit finite witness and projection. The witness carrier and structure
are the previously defined `WitnessVertex B₀ E` and `witnessStructure B₀ E`.
In particular, the combinatorial trichotomy quantifies over arbitrary
vertex subsets, not only substructures or generic sets.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w z
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {α : Type w} {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)
variable (E : L.RelSymbol 2)
variable (hfix : act.FixesRel E) (hcomplete : A.EdgeComplete E)

/-- Finite irreducible-faithful EPPA witnesses admit a finite cycle-sparsening
witness with an irreducible-faithful embedding, a homomorphism-embedding to
the original witness, and the required induced-cycle counting trichotomy. -/
theorem cycleSparseningLemma [Finite β]
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ)
    (heppa : Structure.IsEPPAWitness act ψ) :
    Finite (WitnessVertex B₀ E) ∧
    Structure.IsEPPAWitness act
      (canonicalEmbedding act A B₀ ψ E hfix hcomplete) ∧
    Structure.IsIrreducibleStructureFaithful act
      (canonicalEmbedding act A B₀ ψ E hfix hcomplete) ∧
    Structure.Homomorphism.IsHomomorphismEmbedding act
      (projection act B₀ E) ∧
    ∀ S : Set (WitnessVertex B₀ E),
      ¬ ContainsInducedCycle B₀ E S ∨
      (Set.image (fun w => w.base B₀ E) S).ncard < S.ncard ∨
      Nat.card (EdgePairs (witnessStructure B₀ E) E S) <
        Nat.card (EdgePairs B₀ E
          (Set.image (fun w => w.base B₀ E) S)) := by
  refine ⟨witnessVertex_finite B₀ E, ?_, ?_, ?_, ?_⟩
  · exact sparseningWitness_isEPPAWitness
      act A B₀ ψ E hfix hcomplete heppa
  · exact sparseningWitness_isIrreducibleStructureFaithful
      act A B₀ ψ E hfix hcomplete hfaith
  · exact projection_isHomomorphismEmbedding act B₀ E
  · exact sparsening_trichotomy B₀ E

/-- Moreover, any chosen coherent extension system on the base witness
induces a coherent extension system on the sparsening witness. -/
theorem cycleSparseningLemma_coherent [Finite β]
    (hcoh : Structure.IsCoherentEPPAWitness act ψ) :
    Structure.IsCoherentEPPAWitness act
      (canonicalEmbedding act A B₀ ψ E hfix hcomplete) :=
  sparseningWitness_isCoherentEPPAWitness
    act A B₀ ψ E hfix hcomplete hcoh

end Sparsening
end AllThoseEPPA
