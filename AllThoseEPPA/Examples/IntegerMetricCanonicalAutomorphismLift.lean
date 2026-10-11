import AllThoseEPPA.Examples.IntegerMetricAutomorphismCosts
import AllThoseEPPA.Examples.IntegerMetricCompletionHomEmb

/-!
# Actual automorphism lifts to the canonical metric completion

A source automorphism of a consistent partial distance-coloured
structure acts on the SAME carrier of its canonical shortest-path
metric completion. Existing checked cost-equivariance shows that
it preserves all newly completed distances.

Crucially, no arbitrary extension choice is made. The lifted
automorphism has exactly the same partial equivalence (which is
already total) and the same language component. Consequently
the lifting operation preserves identity, composition, and its
pointwise action by construction. This is the algebraic part of
the automorphism-preserving completion required by the paper.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Lift EVERY original automorphism to an actual automorphism
of the completed metric encoding, using the same vertex map
and the same (trivial) language action. -/
noncomputable def liftAutomorphismToCanonicalCompletion
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (hD : 0 < D)
    (g : Structure.Automorphism (action D) B) :
    Structure.Automorphism (action D)
      (toStructure (toSymmetricCost B hB hD).completedMetric) where
  toPartialIsomorphism := {
    lang := g.lang
    toPartialEquiv := g.toPartialIsomorphism.toPartialEquiv
    source_closed := by
      intro n F xs hxs y hy
      exact F.elim
    target_closed := by
      intro n F xs hxs y hy
      exact F.elim
    map_rel_iff := by
      intro n R xs hxs
      cases R with
      | edge d =>
          simp only [action_on_edge]
          change
            (toSymmetricCost B hB hD).completedMetric.dist
                (g (xs 0)) (g (xs 1)) = d.val + 1 ↔
              (toSymmetricCost B hB hD).completedMetric.dist
                (xs 0) (xs 1) = d.val + 1
          rw [completedMetric_automorphism_isometry B hB hD
            g (xs 0) (xs 1)]
    map_func := by
      intro n F xs hxs
      exact F.elim
  }
  source_eq_univ := g.source_eq_univ
  target_eq_univ := g.target_eq_univ

/-- Lifting does not change the underlying vertex action. -/
theorem liftAutomorphismToCanonicalCompletion_apply
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (hD : 0 < D)
    (g : Structure.Automorphism (action D) B)
    (x : V) :
    liftAutomorphismToCanonicalCompletion B hB hD g x = g x := rfl

/-- Lifting does not change the language action. -/
theorem liftAutomorphismToCanonicalCompletion_lang
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (hD : 0 < D)
    (g : Structure.Automorphism (action D) B) :
    (liftAutomorphismToCanonicalCompletion B hB hD g).lang = g.lang := rfl

/-- The lift of the identity is the identity of the completion. -/
theorem liftAutomorphismToCanonicalCompletion_id
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (hD : 0 < D) :
    liftAutomorphismToCanonicalCompletion B hB hD
      (Structure.Automorphism.id B) =
        Structure.Automorphism.id
          (toStructure (toSymmetricCost B hB hD).completedMetric) := by
  apply Structure.Automorphism.ext_of_lang_apply
  · rfl
  · intro x
    rfl

/-- The canonical lifting respects composition on the nose. -/
theorem liftAutomorphismToCanonicalCompletion_comp
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (hD : 0 < D)
    (g f : Structure.Automorphism (action D) B) :
    liftAutomorphismToCanonicalCompletion B hB hD (g.comp f) =
      (liftAutomorphismToCanonicalCompletion B hB hD g).comp
      (liftAutomorphismToCanonicalCompletion B hB hD f) := by
  apply Structure.Automorphism.ext_of_lang_apply
  · rfl
  · intro x
    rfl

end Bridge
end IntegerMetric
end AllThoseEPPA
