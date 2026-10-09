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

/-- A pointwise move of the projection of `S` into the distinguished copy
is exactly the subset condition needed by the inverse embedding. -/
theorem movedProjection_subset_range
    (S : Set (WitnessVertex act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hg :
      ∀ w, w ∈ S → ∃ a : α, g w.base = ψ a) :
    movedProjection act A B₀ ψ g S ⊆ Set.range ψ := by
  rintro y ⟨b, hb, rfl⟩
  rcases hb with ⟨w, hw, rfl⟩
  rcases hg w hw with ⟨a, ha⟩
  exact ⟨a, ha.symm⟩

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
  change ψ.lang * (ψ.lang⁻¹ * (g.lang * 1)) = g.lang
  simp [mul_assoc]

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
  calc
    ψ (back (move (proj x))) = (move (proj x)).1 := hback
    _ = g x.1.base := rfl


/-- A family consisting pointwise of canonical vertices is generic. -/
theorem witnessFamilyGeneric_of_pointwise_canonical
    {ι : Type*}
    (ws : ι → WitnessVertex act A B₀ ψ)
    (hcanon :
      ∀ i, ∃ a : α,
        ws i = canonicalVertex act A B₀ ψ a) :
    WitnessFamilyGeneric act A B₀ ψ ws := by
  choose as has using hcanon
  have hws :
      ws = fun i => canonicalVertex act A B₀ ψ (as i) := by
    funext i
    exact has i
  rw [hws]
  exact canonicalFamilyGeneric act A B₀ ψ as

/-- The range of the final faithful embedding is generic because every one
of its vertices is canonical. -/
theorem faithfulnessEmbedding_range_generic
    (S : Set (WitnessVertex act A B₀ ψ))
    (hS : (witnessStructure act A B₀ ψ).IsClosed S)
    (hgen : WitnessSetGeneric act A B₀ ψ S)
    (g : Structure.Automorphism act B₀)
    (hsub :
      movedProjection act A B₀ ψ g S ⊆ Set.range ψ) :
    WitnessSetGeneric act A B₀ ψ
      (Set.range
        (faithfulnessEmbedding act A B₀ ψ
          S hS hgen g hsub)) := by
  apply witnessFamilyGeneric_of_pointwise_canonical
    act A B₀ ψ
  intro i
  rcases i with ⟨u, hu⟩
  rcases hu with ⟨x, hxu⟩
  rcases
      faithfulnessEmbedding_isCanonical
        act A B₀ ψ S hS hgen g hsub x with
    ⟨a, hca⟩
  exact ⟨a, hxu.symm.trans hca⟩

/-- **Faithfulness part of Proposition `prop:faithful`.**  Every irreducible
substructure of the faithful witness can be moved into the canonical copy of
the original structure. -/
theorem faithfulWitness_isIrreducibleStructureFaithful [Finite β] :
    Structure.IsIrreducibleStructureFaithful act
      (canonicalEmbedding act A B₀ ψ) := by
  intro S hS hirr
  let hgen :
      WitnessSetGeneric act A B₀ ψ S :=
    irreducible_witnessSetGeneric act A B₀ ψ S hS hirr
  rcases
      irreducible_projection_not_bad
        act A B₀ ψ S hS hirr with
    ⟨g, hg⟩
  let hsub :
      movedProjection act A B₀ ψ g S ⊆ Set.range ψ :=
    movedProjection_subset_range act A B₀ ψ S g hg
  let f :=
    faithfulnessEmbedding act A B₀ ψ
      S hS hgen g hsub
  let p :=
    partialAutomorphismOfInducedEmbedding
      act (witnessStructure act A B₀ ψ)
      S hS f
  have hsource :
      WitnessSetGeneric act A B₀ ψ p.source := by
    simpa [p] using hgen
  have htarget :
      WitnessSetGeneric act A B₀ ψ p.target := by
    simpa [p, inducedEmbeddingRange] using
      (faithfulnessEmbedding_range_generic
        act A B₀ ψ S hS hgen g hsub)
  have hcompat :
      BaseCompatible act A B₀ ψ p g := by
    constructor
    · change g.lang = f.lang
      exact
        (faithfulnessEmbedding_lang
          act A B₀ ψ S hS hgen g hsub).symm
    · intro x hx
      have hxS : x ∈ S := by
        simpa [p] using hx
      have hp :=
        partialAutomorphismOfInducedEmbedding_apply
          act (witnessStructure act A B₀ ψ)
          S hS f hxS
      rw [hp]
      exact
        (faithfulnessEmbedding_base
          act A B₀ ψ S hS hgen g hsub
          ⟨x, hxS⟩).symm
  rcases
      faithfulExtension act A B₀ ψ
        p g hsource htarget hcompat with
    ⟨h, hext⟩
  refine ⟨h, ?_⟩
  intro x hx
  let sx : S := ⟨x, hx⟩
  rcases
      faithfulnessEmbedding_isCanonical
        act A B₀ ψ S hS hgen g hsub sx with
    ⟨a, hfa⟩
  refine ⟨a, ?_⟩
  have hxSource : x ∈ p.source := by
    simpa [p] using hx
  have hextx := hext.2 x hxSource
  have hp :=
    partialAutomorphismOfInducedEmbedding_apply
      act (witnessStructure act A B₀ ψ)
      S hS f hx
  change h x = canonicalEmbedding act A B₀ ψ a
  calc
    h x = p x := by
      simpa [Structure.Embedding.id] using hextx
    _ = f sx := by
      simpa [sx] using hp
    _ = canonicalVertex act A B₀ ψ a := hfa
    _ = canonicalEmbedding act A B₀ ψ a := rfl

end Faithful
end AllThoseEPPA
