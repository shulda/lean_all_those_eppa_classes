import AllThoseEPPA.Examples.IntegerMetricBridge
import AllThoseEPPA.Map

/-!
# Homomorphisms of complete metric colour structures are isometries

This is a key semantic regression for the metric EPPA application.

The relational encoding of a D-bounded integer metric has precisely
one positive distance colour on every ordered pair of distinct
vertices, with zero distance represented by equality. Consequently
ANY Γ-homomorphism between TWO encoded metrics must preserve every
distance exactly and must be injective, even though a general
homomorphism of incomplete coloured structures need not be injective.

Thus at the metric end of a local completion, a homomorphism-embedding
on a source labelled edge preserves that edge's actual length simply
by positive relation preservation, without needing global injection
on the incomplete source.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Every positive integer d≤D has the unique distance colour
with index d-1. This works uniformly for arbitrary D and becomes
vacuous when D=0. -/
private def positiveDistanceIndex {D d : ℕ}
    (hpos : 0 < d) (hBound : d ≤ D) : Fin D :=
  ⟨d - 1, by omega⟩

/-- A homomorphism of the complete distance-colour encodings
preserves all integer distances, with no injectivity hypothesis
on the vertex map. -/
theorem homomorphism_preserves_distance
    {D : ℕ} {V W : Type u}
    (M : BoundedNatMetric D V) (N : BoundedNatMetric D W)
    (f : Structure.Homomorphism (action D)
      (toStructure M) (toStructure N))
    (x y : V) :
    N.dist (f x) (f y) = M.dist x y := by
  by_cases hxy : x = y
  · subst y
    rw [N.dist_self, M.dist_self]
  · have hpos : 0 < M.dist x y :=
      M.toNatMetric.dist_pos hxy
    have hBound : M.dist x y ≤ D := M.dist_le x y
    let d : Fin D :=
      positiveDistanceIndex hpos hBound
    have hd : d.val + 1 = M.dist x y := by
      change (M.dist x y - 1) + 1 = M.dist x y
      omega
    have hRel :
        (toStructure M).rel (RelSymbol.edge d) ![x, y] := by
      change M.dist x y = d.val + 1
      exact hd.symm
    have hImage :=
      f.map_rel (RelSymbol.edge d) ![x, y] hRel
    have hImage' :
        N.dist (f x) (f y) = d.val + 1 := by
      change (toStructure N).rel (RelSymbol.edge d)
        (f.toFun ∘ ![x, y])
      simpa only [action_on_edge] using hImage
    exact hImage'.trans hd

/-- A homomorphism between full metric encodings is
automatically injective, since positive distance cannot map
to a zero distance. -/
theorem homomorphism_injective
    {D : ℕ} {V W : Type u}
    (M : BoundedNatMetric D V) (N : BoundedNatMetric D W)
    (f : Structure.Homomorphism (action D)
      (toStructure M) (toStructure N)) :
    Function.Injective f.toFun := by
  intro x y hxy
  apply M.eq_of_dist_eq_zero
  have hDist := homomorphism_preserves_distance M N f x y
  rw [hxy, N.dist_self] at hDist
  exact hDist.symm

/-- Homomorphisms between genuine complete integer metrics
are actually exact relational embeddings. This is NOT
asserted for incomplete partial metric structures. -/
def homomorphism_toEmbedding
    {D : ℕ} {V W : Type u}
    (M : BoundedNatMetric D V) (N : BoundedNatMetric D W)
    (f : Structure.Homomorphism (action D)
      (toStructure M) (toStructure N)) :
    Structure.Embedding (action D) (toStructure M) (toStructure N) where
  lang := f.lang
  toFun := f.toFun
  injective := homomorphism_injective M N f
  map_rel_iff := by
    intro n R xs
    cases R with
    | edge d =>
        have hdist := homomorphism_preserves_distance
          M N f (xs 0) (xs 1)
        change N.dist (f (xs 0)) (f (xs 1)) =
            d.val + 1 ↔ M.dist (xs 0) (xs 1) = d.val + 1
        rw [hdist]
  map_func := by
    intro n F xs
    exact F.elim

end Bridge
end IntegerMetric
end AllThoseEPPA
