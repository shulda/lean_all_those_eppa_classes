import AllThoseEPPA.CycleSparseningProjectionImage

/-!
# Moving irreducible projections into the distinguished base copy

This is the direct use of irreducible-structure faithfulness of B₀, after
the projection of an irreducible sparsening substructure has been shown
to be a closed irreducible base substructure.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w z
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} {α : Type z}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)
variable (A : Structure L α)
variable (ψ : Structure.Embedding act A B₀)

/-- The base faithfulness hypothesis moves the projected points of every
closed irreducible sparsening substructure into the canonical copy of A. -/
theorem irreducible_projection_moves_into_base_copy
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ)
    (S : Set (WitnessVertex B₀ E))
    (hS : (witnessStructure B₀ E).IsClosed S)
    (hirr : ((witnessStructure B₀ E).induce S hS).IsIrreducible) :
    ∃ g : Structure.Automorphism act B₀,
      ∀ w, w ∈ S → ∃ a : α, g (w.base B₀ E) = ψ a := by
  rcases hfaith
      (projectionImage B₀ E S)
      (projectionImage_isClosed act B₀ E S hS)
      (projectionImage_isIrreducible act B₀ E S hS hirr)
      with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  intro w hw
  exact hg (w.base B₀ E) ⟨w, hw, rfl⟩

end Sparsening
end AllThoseEPPA
