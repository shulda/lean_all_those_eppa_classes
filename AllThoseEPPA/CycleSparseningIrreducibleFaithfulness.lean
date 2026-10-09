import AllThoseEPPA.CycleSparseningFaithfulnessEmbedding

/-!
# Irreducible-structure faithfulness of the cycle-sparsening witness

This is the final use of the generic partial extension lemma: every
irreducible substructure of the sparsening witness can be moved into the
canonical copy of A whenever the base witness B₀ was irreducible-faithful.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {α : Type w} {V : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L V)
variable (ψ : Structure.Embedding act A B₀)
variable (E : L.RelSymbol 2)
variable (hfix : act.FixesRel E) (hcomplete : A.EdgeComplete E)

/-- **Faithfulness part of Lemma `lem:sparsen`.**  Every irreducible
substructure of the cycle-sparsening witness can be moved into the canonical copy of
the original structure. -/
theorem sparseningWitness_isIrreducibleStructureFaithful [Finite V]
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ) :
    Structure.IsIrreducibleStructureFaithful act
      (canonicalEmbedding act A B₀ ψ E hfix hcomplete) := by
  intro S hS hirr
  let hgen :
      WitnessSetGeneric B₀ E S :=
    irreducible_witnessSetGeneric B₀ E S hS hirr
  rcases
      irreducible_projection_moves_into_base_copy
        act B₀ E A ψ hfaith S hS hirr with
    ⟨g, hg⟩
  let hsub :
      movedProjection act B₀ E g S ⊆ Set.range ψ :=
    movedProjection_subset_range act A B₀ ψ E S g hg
  let f :=
    faithfulnessEmbedding act A B₀ ψ E hfix hcomplete
      S hS hgen g hsub
  let p :=
    Faithful.partialAutomorphismOfInducedEmbedding
      act (witnessStructure B₀ E)
      S hS f
  have hsource :
      WitnessSetGeneric B₀ E p.source := by
    simpa [p] using hgen
  have htarget :
      WitnessSetGeneric B₀ E p.target := by
    simpa [p, Faithful.inducedEmbeddingRange] using
      (faithfulnessEmbedding_range_generic
        act A B₀ ψ E hfix hcomplete S hS hgen g hsub)
  have hcompat :
      BaseCompatible act B₀ E p g := by
    constructor
    · change g.lang = f.lang
      exact
        (faithfulnessEmbedding_lang
          act A B₀ ψ E hfix hcomplete S hS hgen g hsub).symm
    · intro x hx
      have hxS : x ∈ S := by
        simpa [p] using hx
      have hp :=
        Faithful.partialAutomorphismOfInducedEmbedding_apply
          act (witnessStructure B₀ E)
          S hS f hxS
      rw [hp]
      exact
        (faithfulnessEmbedding_base
          act A B₀ ψ E hfix hcomplete S hS hgen g hsub
          ⟨x, hxS⟩).symm
  rcases
      sparseningExtension act B₀ E
        p g hfix hcompat hsource htarget with
    ⟨h, hext⟩
  refine ⟨h, ?_⟩
  intro x hx
  let sx : S := ⟨x, hx⟩
  rcases
      faithfulnessEmbedding_isCanonical
        act A B₀ ψ E hfix hcomplete S hS hgen g hsub sx with
    ⟨a, hfa⟩
  refine ⟨a, ?_⟩
  have hxSource : x ∈ p.source := by
    simpa [p] using hx
  have hextx := hext.2 x hxSource
  have hp :=
    Faithful.partialAutomorphismOfInducedEmbedding_apply
      act (witnessStructure B₀ E)
      S hS f hx
  change h x = canonicalEmbedding act A B₀ ψ E hfix hcomplete a
  calc
    h x = p x := by
      simpa [Structure.Embedding.id] using hextx
    _ = f sx := by
      simpa [sx] using hp
    _ = canonicalVertex act A B₀ ψ E hfix hcomplete a := hfa
    _ = canonicalEmbedding act A B₀ ψ E hfix hcomplete a := rfl


end Sparsening
end AllThoseEPPA
