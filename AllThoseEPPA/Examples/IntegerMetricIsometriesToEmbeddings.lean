import AllThoseEPPA.Examples.IntegerMetricBridge

/-!
# Genuine isometric maps induce relational embeddings

In the complete binary metric encoding, preserving the integer
distance function is equivalent to being an exact relational
embedding. This is one direction, needed to convert the two
isometries of a metric amalgam back into the Γ-embedding
interface of the manuscript's amalgamation class.

Global injectivity does not need to be stipulated separately:
it follows from preserving all metric distances.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u v

theorem distancePreserving_injective
    {D : ℕ} {V : Type u} {W : Type v}
    (A : BoundedNatMetric D V)
    (B : BoundedNatMetric D W)
    (f : V → W)
    (hDist : ∀ x y : V,
      B.dist (f x) (f y) = A.dist x y) :
    Function.Injective f := by
  intro x y hxy
  apply A.eq_of_dist_eq_zero
  rw [← hDist x y, hxy, B.toNatMetric.dist_self]

/-- Isometric point maps yield exact relational embeddings in
the full distance-labelled graph language, for arbitrary D
(including D=0), without finiteness assumptions. -/
noncomputable def encodingEmbeddingOfDistancePreserving
    {D : ℕ} {V : Type u} {W : Type v}
    (A : BoundedNatMetric D V)
    (B : BoundedNatMetric D W)
    (f : V → W)
    (hDist : ∀ x y : V,
      B.dist (f x) (f y) = A.dist x y) :
    Structure.Embedding (action D) (toStructure A) (toStructure B) where
  lang := 1
  toFun := f
  injective := distancePreserving_injective A B f hDist
  map_rel_iff := by
    intro n R xs
    cases R with
    | edge d =>
        simp only [action_on_edge]
        change
          B.dist (f (xs 0)) (f (xs 1)) = d.val + 1 ↔
          A.dist (xs 0) (xs 1) = d.val + 1
        rw [hDist (xs 0) (xs 1)]
  map_func := by
    intro n F xs
    exact F.elim

end Bridge
end IntegerMetric
end AllThoseEPPA
