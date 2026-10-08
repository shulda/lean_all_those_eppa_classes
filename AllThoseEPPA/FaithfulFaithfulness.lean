import AllThoseEPPA.FaithfulEmbeddingInverse

/-!
# Irreducible-structure faithfulness of the faithful witness

This file packages the final part of Proposition `prop:faithful`: every
irreducible substructure of the faithful witness can be moved into the
canonical copy of the original structure.
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

/-- Move the projection image of a witness subset by a base automorphism. -/
def movedProjection
    (g : Structure.Automorphism act B₀)
    (S : Set (WitnessVertex act A B₀ ψ)) :
    Set β :=
  g '' projectionImage act A B₀ ψ S

/-- The moved projection image of a closed witness subset is closed. -/
theorem movedProjection_isClosed
    (g : Structure.Automorphism act B₀)
    (S : Set (WitnessVertex act A B₀ ψ))
    (hS : (witnessStructure act A B₀ ψ).IsClosed S) :
    B₀.IsClosed (movedProjection act A B₀ ψ g S) := by
  exact
    automorphism_image_isClosed act B₀ g
      (projectionImage_isClosed act A B₀ ψ S hS)

/-- Compose projection, a base automorphism, inverse projection to `A` on
the moved image, and the canonical embedding back into the faithful witness. -/
noncomputable def faithfulnessEmbedding
    (S : Set (WitnessVertex act A B₀ ψ))
    (hS : (witnessStructure act A B₀ ψ).IsClosed S)
    (hgen : WitnessSetGeneric act A B₀ ψ S)
    (g : Structure.Automorphism act B₀)
    (hsub :
      movedProjection act A B₀ ψ g S ⊆ Set.range ψ) :
    Structure.Embedding act
      ((witnessStructure act A B₀ ψ).induce S hS)
      (witnessStructure act A B₀ ψ) := by
  let proj :=
    projectionInducedEmbedding act A B₀ ψ S hS hgen
  let move :=
    automorphismInducedEmbedding act B₀ g
      (projectionImage act A B₀ ψ S)
      (projectionImage_isClosed act A B₀ ψ S hS)
  let back :=
    embeddingInverseOnClosedSubset act ψ
      (movedProjection act A B₀ ψ g S)
      (movedProjection_isClosed act A B₀ ψ g S hS)
      hsub
  exact
    (canonicalEmbedding act A B₀ ψ).comp
      (back.comp (move.comp proj))

/-- The faithful embedding used for the final move has the same language
component as the chosen base automorphism. -/
theorem faithfulnessEmbedding_lang
    (S : Set (WitnessVertex act A B₀ ψ))
    (hS : (witnessStructure act A B₀ ψ).IsClosed S)
    (hgen : WitnessSetGeneric act A B₀ ψ S)
    (g : Structure.Automorphism act B₀)
    (hsub :
      movedProjection act A B₀ ψ g S ⊆ Set.range ψ) :
    (faithfulnessEmbedding act A B₀ ψ
      S hS hgen g hsub).lang = g.lang := by
  simp [faithfulnessEmbedding,
    Structure.Embedding.comp,
    embeddingInverseOnClosedSubset]

/-- Every point of the final embedding lands at a canonical witness vertex. -/
theorem faithfulnessEmbedding_isCanonical
    (S : Set (WitnessVertex act A B₀ ψ))
    (hS : (witnessStructure act A B₀ ψ).IsClosed S)
    (hgen : WitnessSetGeneric act A B₀ ψ S)
    (g : Structure.Automorphism act B₀)
    (hsub :
      movedProjection act A B₀ ψ g S ⊆ Set.range ψ)
    (x : S) :
    ∃ a : α,
      faithfulnessEmbedding act A B₀ ψ
          S hS hgen g hsub x =
        canonicalVertex act A B₀ ψ a := by
  let proj :=
    projectionInducedEmbedding act A B₀ ψ S hS hgen
  let move :=
    automorphismInducedEmbedding act B₀ g
      (projectionImage act A B₀ ψ S)
      (projectionImage_isClosed act A B₀ ψ S hS)
  let back :=
    embeddingInverseOnClosedSubset act ψ
      (movedProjection act A B₀ ψ g S)
      (movedProjection_isClosed act A B₀ ψ g S hS)
      hsub
  let a : α := back (move (proj x))
  exact ⟨a, rfl⟩

/-- On base coordinates the final faithful embedding is exactly the chosen
base automorphism. -/
theorem faithfulnessEmbedding_base
    (S : Set (WitnessVertex act A B₀ ψ))
    (hS : (witnessStructure act A B₀ ψ).IsClosed S)
    (hgen : WitnessSetGeneric act A B₀ ψ S)
    (g : Structure.Automorphism act B₀)
    (hsub :
      movedProjection act A B₀ ψ g S ⊆ Set.range ψ)
    (x : S) :
    (faithfulnessEmbedding act A B₀ ψ
        S hS hgen g hsub x).base =
      g x.1.base := by
  let proj :=
    projectionInducedEmbedding act A B₀ ψ S hS hgen
  let move :=
    automorphismInducedEmbedding act B₀ g
      (projectionImage act A B₀ ψ S)
      (projectionImage_isClosed act A B₀ ψ S hS)
  let back :=
    embeddingInverseOnClosedSubset act ψ
      (movedProjection act A B₀ ψ g S)
      (movedProjection_isClosed act A B₀ ψ g S hS)
      hsub
  have hback :=
    embeddingInverseOnClosedSubset_apply_spec
      act ψ
      (movedProjection act A B₀ ψ g S)
      (movedProjection_isClosed act A B₀ ψ g S hS)
      hsub (move (proj x))
  change ψ (back (move (proj x))) = g x.1.base
  simpa [back, move, proj, movedProjection,
    WitnessVertex.base] using hback

end Faithful
end AllThoseEPPA
