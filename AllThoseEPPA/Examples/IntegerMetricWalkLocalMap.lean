import AllThoseEPPA.Examples.IntegerMetricSmallPairCompletions
import AllThoseEPPA.Examples.IntegerMetricShortWalkColours
import AllThoseEPPA.Examples.IntegerMetricLocalCertificates

/-!
# Metric walk certificates from preserved old relational edges

For the final metric shortest-path completion, small induced
substructures are ordinarily homomorphism-embedded into genuine
metrics. Their maps need not be injective on the whole original
structure, and the shortest-path candidate assigns default costs
on uncoloured pairs that the maps need not preserve.

The correct local statement is therefore about WALK SUPPORTS.

If a walk uses only originally coloured edges, every point of
the walk belongs to a subset S, and a map from the original
vertices into some metric preserves every old distance-colour
edge whose endpoints lie in S, then that walk is mapped to
a metric walk with the exact same individual edge weights.

Consequently the triangle inequality in the target rules out
any shortcut whose endpoints also retain their original
distance. No injectivity assumption enters this lemma.

The next step constructs the required map from a genuine
ordinary homomorphism-embedding completion of the induced
substructure on the finite walk support (at most D vertices).
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u

namespace Walk

/-- Every edge of an already-labelled walk is measured exactly
by a metric map preserving old colour relations on a superset of
the walk support. No global injectivity of that map is assumed.

This is parametrized by the exact metric-level edge preservation
interface, so the subsequent application to actual local
homomorphism-embeddings is a separate, auditable step. -/
theorem edgesPreserved_of_coloured_and_localRelationMap
    {D : ℕ} {V W : Type u} [DecidableEq V]
    (B : Structure (Bridge.language D) V)
    (hB : Bridge.IsConsistentPartialMetric B)
    (hD : 0 < D)
    (M : NatMetric W)
    (f : V → W)
    (S : Set V)
    (hRel :
      ∀ (d : Fin D) (a b : V),
        a ∈ S → b ∈ S →
        B.rel (Bridge.RelSymbol.edge d) ![a, b] →
        M.dist (f a) (f b) = d.val + 1)
    {x y : V} (p : Walk V x y)
    (hColoured : p.AllEdgesColoured B)
    (hSubset : ∀ v : V, v ∈ p.support → v ∈ S) :
    p.EdgesPreserved (Bridge.toSymmetricCost B hB hD) M f := by
  revert hColoured hSubset
  induction p with
  | nil a =>
      intro _ _
      trivial
  | @step a b z hab tail ih =>
      intro hColour hSub
      obtain ⟨⟨d, hd⟩, hTailColour⟩ := hColour
      have ha : a ∈ S :=
        hSub a (by simp [Walk.support])
      have hb : b ∈ S := by
        apply hSub b
        change b ∈ insert a tail.support
        exact Finset.mem_insert_of_mem tail.start_mem_support
      have hTailSub : ∀ v : V,
          v ∈ tail.support → v ∈ S := by
        intro v hv
        apply hSub v
        change v ∈ insert a tail.support
        exact Finset.mem_insert_of_mem hv
      have hOldCost :
          (Bridge.toSymmetricCost B hB hD).cost a b =
            d.val + 1 :=
        Bridge.toSymmetricCost_edge B hB hD d hd
      have hMetricCost : M.dist (f a) (f b) = d.val + 1 :=
        hRel d a b ha hb hd
      have hNext :=
        ih hTailColour hTailSub
      change M.dist (f a) (f b) =
          (Bridge.toSymmetricCost B hB hD).cost a b ∧
            tail.EdgesPreserved
              (Bridge.toSymmetricCost B hB hD) M f
      exact ⟨hMetricCost.trans hOldCost.symm, hNext⟩

end Walk
end IntegerMetric
end AllThoseEPPA
