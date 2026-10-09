import AllThoseEPPA.CycleSparseningProjectionFaithfulness
import AllThoseEPPA.FaithfulFaithfulness

/-!
# Moving irreducible sparsening substructures into their canonical copy

This adapts the already checked construction from the cycle-sparsening witness:
project the generic induced structure, move its projection in the base,
invert the original embedding, then include it canonically into the
cycle-sparsening witness.
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

/-- Move the projection image of a witness subset by a base automorphism. -/
def movedProjection
    (g : Structure.Automorphism act B₀)
    (S : Set (WitnessVertex B₀ E)) :
    Set V :=
  g '' projectionImage B₀ E S

/-- The moved projection image of a closed witness subset is closed. -/
theorem movedProjection_isClosed
    (g : Structure.Automorphism act B₀)
    (S : Set (WitnessVertex B₀ E))
    (hS : (witnessStructure B₀ E).IsClosed S) :
    B₀.IsClosed (movedProjection act B₀ E g S) := by
  exact
    Faithful.automorphism_image_isClosed act B₀ g
      (projectionImage_isClosed act B₀ E S hS)

/-- A pointwise move of the projection of `S` into the distinguished copy
is exactly the subset condition needed by the inverse embedding. -/
theorem movedProjection_subset_range
    (S : Set (WitnessVertex B₀ E))
    (g : Structure.Automorphism act B₀)
    (hg :
      ∀ w, w ∈ S → ∃ a : α, g (w.base B₀ E) = ψ a) :
    movedProjection act B₀ E g S ⊆ Set.range ψ := by
  rintro y ⟨b, hb, rfl⟩
  rcases hb with ⟨w, hw, rfl⟩
  rcases hg w hw with ⟨a, ha⟩
  exact ⟨a, ha.symm⟩

/-- Compose projection, a base automorphism, inverse projection to `A` on
the moved image, and the canonical embedding back into the cycle-sparsening witness. -/
noncomputable def faithfulnessEmbedding
    (S : Set (WitnessVertex B₀ E))
    (hS : (witnessStructure B₀ E).IsClosed S)
    (hgen : WitnessSetGeneric B₀ E S)
    (g : Structure.Automorphism act B₀)
    (hsub :
      movedProjection act B₀ E g S ⊆ Set.range ψ) :
    Structure.Embedding act
      ((witnessStructure B₀ E).induce S hS)
      (witnessStructure B₀ E) := by
  let proj :=
    projectionInducedEmbedding act B₀ E S hS hgen
  let move :=
    Faithful.automorphismInducedEmbedding act B₀ g
      (projectionImage B₀ E S)
      (projectionImage_isClosed act B₀ E S hS)
  let back :=
    Faithful.embeddingInverseOnClosedSubset act ψ
      (movedProjection act B₀ E g S)
      (movedProjection_isClosed act B₀ E g S hS)
      hsub
  exact
    (canonicalEmbedding act A B₀ ψ E hfix hcomplete).comp
      (back.comp (move.comp proj))

/-- The faithful embedding used for the final move has the same language
component as the chosen base automorphism. -/
theorem faithfulnessEmbedding_lang
    (S : Set (WitnessVertex B₀ E))
    (hS : (witnessStructure B₀ E).IsClosed S)
    (hgen : WitnessSetGeneric B₀ E S)
    (g : Structure.Automorphism act B₀)
    (hsub :
      movedProjection act B₀ E g S ⊆ Set.range ψ) :
    (faithfulnessEmbedding act A B₀ ψ E hfix hcomplete
      S hS hgen g hsub).lang = g.lang := by
  change ψ.lang * (ψ.lang⁻¹ * (g.lang * 1)) = g.lang
  simp [mul_assoc]

/-- Every point of the final embedding lands at a canonical witness vertex. -/
theorem faithfulnessEmbedding_isCanonical
    (S : Set (WitnessVertex B₀ E))
    (hS : (witnessStructure B₀ E).IsClosed S)
    (hgen : WitnessSetGeneric B₀ E S)
    (g : Structure.Automorphism act B₀)
    (hsub :
      movedProjection act B₀ E g S ⊆ Set.range ψ)
    (x : S) :
    ∃ a : α,
      faithfulnessEmbedding act A B₀ ψ E hfix hcomplete
          S hS hgen g hsub x =
        canonicalVertex act A B₀ ψ E hfix hcomplete a := by
  let proj :=
    projectionInducedEmbedding act B₀ E S hS hgen
  let move :=
    Faithful.automorphismInducedEmbedding act B₀ g
      (projectionImage B₀ E S)
      (projectionImage_isClosed act B₀ E S hS)
  let back :=
    Faithful.embeddingInverseOnClosedSubset act ψ
      (movedProjection act B₀ E g S)
      (movedProjection_isClosed act B₀ E g S hS)
      hsub
  let a : α := back (move (proj x))
  exact ⟨a, rfl⟩

/-- On base coordinates the final faithful embedding is exactly the chosen
base automorphism. -/
theorem faithfulnessEmbedding_base
    (S : Set (WitnessVertex B₀ E))
    (hS : (witnessStructure B₀ E).IsClosed S)
    (hgen : WitnessSetGeneric B₀ E S)
    (g : Structure.Automorphism act B₀)
    (hsub :
      movedProjection act B₀ E g S ⊆ Set.range ψ)
    (x : S) :
    (faithfulnessEmbedding act A B₀ ψ E hfix hcomplete
        S hS hgen g hsub x).base B₀ E =
      g (x.1.base B₀ E) := by
  let proj :=
    projectionInducedEmbedding act B₀ E S hS hgen
  let move :=
    Faithful.automorphismInducedEmbedding act B₀ g
      (projectionImage B₀ E S)
      (projectionImage_isClosed act B₀ E S hS)
  let back :=
    Faithful.embeddingInverseOnClosedSubset act ψ
      (movedProjection act B₀ E g S)
      (movedProjection_isClosed act B₀ E g S hS)
      hsub
  have hback :=
    Faithful.embeddingInverseOnClosedSubset_apply_spec
      act ψ
      (movedProjection act B₀ E g S)
      (movedProjection_isClosed act B₀ E g S hS)
      hsub (move (proj x))
  change ψ (back (move (proj x))) = g (x.1.base B₀ E)
  calc
    ψ (back (move (proj x))) = (move (proj x)).1 := hback
    _ = g (x.1.base B₀ E) := rfl


/-- A family consisting pointwise of canonical vertices is generic. -/
theorem witnessFamilyGeneric_of_pointwise_canonical
    {ι : Type*}
    (ws : ι → WitnessVertex B₀ E)
    (hcanon :
      ∀ i, ∃ a : α,
        ws i = canonicalVertex act A B₀ ψ E hfix hcomplete a) :
    WitnessFamilyGeneric B₀ E ws := by
  choose as has using hcanon
  have hws :
      ws = fun i => canonicalVertex act A B₀ ψ E hfix hcomplete (as i) := by
    funext i
    exact has i
  rw [hws]
  exact canonicalFamilyGeneric act A B₀ ψ E hfix hcomplete as

/-- The range of the final faithful embedding is generic because every one
of its vertices is canonical. -/
theorem faithfulnessEmbedding_range_generic
    (S : Set (WitnessVertex B₀ E))
    (hS : (witnessStructure B₀ E).IsClosed S)
    (hgen : WitnessSetGeneric B₀ E S)
    (g : Structure.Automorphism act B₀)
    (hsub :
      movedProjection act B₀ E g S ⊆ Set.range ψ) :
    WitnessSetGeneric B₀ E
      (Set.range
        (faithfulnessEmbedding act A B₀ ψ E hfix hcomplete
          S hS hgen g hsub)) := by
  apply witnessFamilyGeneric_of_pointwise_canonical
    act A B₀ ψ E hfix hcomplete
  intro i
  rcases i with ⟨u, hu⟩
  rcases hu with ⟨x, hxu⟩
  rcases
      faithfulnessEmbedding_isCanonical
        act A B₀ ψ E hfix hcomplete S hS hgen g hsub x with
    ⟨a, hca⟩
  exact ⟨a, hxu.symm.trans hca⟩

end Sparsening
end AllThoseEPPA
