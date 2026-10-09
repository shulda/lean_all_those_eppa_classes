import AllThoseEPPA.CycleSparseningParityProjection

/-!
# Extra E-edge in the projection of a bad witness cycle

A bad induced cycle in the sparsening witness whose projection is
injective must acquire a new edge in the base witness. This is the
direct combinatorial precursor to the strict edge-count inequality
in the sparsening trichotomy.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions] {V : Type v}
variable (B₀ : Structure L V) (E : L.RelSymbol 2)

/-- When the base projection is injective on an induced bad witness cycle,
there are two vertices on that cycle with an E-edge between their
projections in B₀ but no E-edge between the original witness vertices. -/
theorem extra_projection_edge_of_bad_cycle
    (c : Structure.BadCycleSequence (witnessStructure B₀ E) E)
    (hinj : Set.InjOn
      (fun w : WitnessVertex B₀ E => w.base B₀ E) c.carrier) :
    ∃ x y : WitnessVertex B₀ E,
      x ∈ c.carrier ∧ y ∈ c.carrier ∧
      B₀.Edge E (x.base B₀ E) (y.base B₀ E) ∧
      ¬ (witnessStructure B₀ E).Edge E x y := by
  classical
  by_contra hnone
  have hreflect :
      ∀ ⦃x y : WitnessVertex B₀ E⦄,
        x ∈ c.carrier → y ∈ c.carrier →
        B₀.Edge E (x.base B₀ E) (y.base B₀ E) →
          (witnessStructure B₀ E).Edge E x y := by
    intro x y hx hy hxy
    by_contra hbad
    exact hnone ⟨x, y, hx, hy, hxy, hbad⟩
  exact no_induced_cycle_of_projection_E_embedding
    B₀ E c hinj hreflect

end Sparsening
end AllThoseEPPA
