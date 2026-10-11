import AllThoseEPPA.Examples.IntegerMetricWalkLocalMap

/-!
# Bounded ordinary metric completions preserve all old edge lengths

This is the main missing local-shortcut implication for the finite
integer-metric EPPA regression.

Let B be an arbitrary finite distance-coloured relational
structure in the language with colours 1,...,D. Assume that
**every induced subset of at most max(D,2) vertices** has an
ordinary homomorphism-embedding into SOME genuine D-metric.

Then:
1. From completions of pairs, the old distance colours have
   no loops, are symmetric, and are unique.
2. Assign the old edge lengths and the default cost D to
   missing edges.
3. If a shortest-path completion shortened an old d-edge,
   some witness walk would have fewer than d steps and
   at most D vertices, and *all its steps would already
   be old labelled edges* (unlabelled steps cost D).
4. Complete the induced subset on that walk's support.
   Its homomorphism preserves the endpoint d-edge AND
   every labelled walk step. Apply the triangle inequality
   in the metric target to contradict the shortcut.

Crucially the ordinary local map is NOT assumed globally
injective. This result supplies the concrete local
preservation lemma, with the same explicit bound max(D,2)
as the expected locally finite completion criterion.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Convert an actual local relational homomorphism to a
true metric into an edge-colour-preserving map on the
original support S. Points outside S are sent to a fixed
basepoint of S; their images play no role in a walk whose
support is included in S. -/
private theorem inducedMetricHom_preservesOldEdge_on_support
    {D : ℕ} {V W : Type u}
    (B : Structure (language D) V)
    (S : Set V)
    (M : BoundedNatMetric D W)
    (f : Structure.Homomorphism (action D)
      (B.induce S (allSubsetsClosed B S))
      (toStructure M))
    (F : V → W)
    (hAgree : ∀ v : V, (hv : v ∈ S) →
      F v = f ⟨v, hv⟩)
    (d : Fin D) (a b : V)
    (ha : a ∈ S) (hb : b ∈ S)
    (hd : B.rel (RelSymbol.edge d) ![a,b]) :
    M.dist (F a) (F b) = d.val + 1 := by
  let A : S := ⟨a,ha⟩
  let C : S := ⟨b,hb⟩
  have hRel :
      (B.induce S (allSubsetsClosed B S)).rel
        (RelSymbol.edge d) ![A,C] := by
    change B.rel (RelSymbol.edge d)
      (Subtype.val ∘ ![A,C])
    have ht :
        (Subtype.val ∘ (![A,C] : Fin 2 → S)) =
          (![a,b] : Fin 2 → V) := by
      funext i
      fin_cases i <;> rfl
    rw [ht]
    exact hd
  have hImage := f.map_rel (RelSymbol.edge d) ![A,C] hRel
  have hDistance :
      M.dist (f A) (f C) = d.val + 1 := by
    change (toStructure M).rel (RelSymbol.edge d)
      (f.toFun ∘ ![A,C])
    simpa only [action_on_edge] using hImage
  calc
    M.dist (F a) (F b) =
        M.dist (f A) (f C) := by
          rw [hAgree a ha, hAgree b hb]
    _ = d.val + 1 := hDistance

/-- **Concrete metric local-finiteness lemma.** If every
induced subset of a finite partially distance-coloured
structure of size ≤ max(D,2) ordinarily
homomorphism-embeds into a genuine D-metric, then the
structure has consistent direct costs and shortest-path
completion preserves the exact length of EVERY already
coloured positive-distance edge.

No global injectivity, no prior metric triangle inequalities
on B, and no extra assumption of consistency of colours. -/
theorem canonicalCompletion_preserves_oldEdges_of_smallMetricCompletions
    {D : ℕ} {V : Type u} [Finite V]
    (B : Structure (language D) V)
    (hD : 0 < D)
    (hSmall :
      HasSmallMetricHomEmbCompletions B (max D 2)) :
    ∃ (hB : IsConsistentPartialMetric B),
      ∀ (d : Fin D) (x y : V),
        B.rel (RelSymbol.edge d) ![x,y] →
        (toSymmetricCost B hB hD).completedMetric.dist x y =
          d.val + 1 := by
  classical
  have hSmallPair : HasSmallMetricHomEmbCompletions B 2 := by
    intro S hCard
    exact hSmall S (hCard.trans (le_max_right D 2))
  let hB : IsConsistentPartialMetric B :=
    consistent_of_smallPairMetricCompletions B hSmallPair
  refine ⟨hB, ?_⟩
  intro d x y hd
  let C : SymmetricCost D V := toSymmetricCost B hB hD
  have hCost : C.cost x y = d.val + 1 :=
    toSymmetricCost_edge B hB hD d hd
  have hShortest : C.shortest x y = C.cost x y := by
    apply (C.shortest_eq_cost_iff_no_shortcut x y).2
    intro p
    by_contra hNot
    have hShort : p.weight C < C.cost x y :=
      Nat.lt_of_not_ge hNot
    have hSmallSupport : p.support.card ≤ D :=
      p.support_card_le_diameter_of_shortcut C hShort
    let S : Set V := p.support
    have hSCard : S.ncard ≤ max D 2 := by
      have hCardEq : S.ncard = p.support.card := by
        exact Set.ncard_coe_finset p.support
      exact hCardEq.le.trans
        (hSmallSupport.trans (le_max_left D 2))
    obtain ⟨W, M, f, hf⟩ := hSmall S hSCard
    have hx : x ∈ S := p.start_mem_support
    have hy : y ∈ S := p.end_mem_support
    let X : S := ⟨x,hx⟩
    let F : V → W := fun z =>
      if hz : z ∈ S then f ⟨z,hz⟩ else f X
    have hAgree (z : V) (hz : z ∈ S) :
        F z = f ⟨z,hz⟩ := by
      simp [F, hz]
    have hOldRel :
        ∀ (e : Fin D) (a b : V),
          a ∈ S → b ∈ S →
          B.rel (RelSymbol.edge e) ![a,b] →
          M.dist (F a) (F b) = e.val + 1 := by
      intro e a b ha hb hab
      exact inducedMetricHom_preservesOldEdge_on_support
        B S M f F hAgree e a b ha hb hab
    have hShortD : p.weight C < D :=
      hShort.trans_le (C.cost_le x y)
    have hColours : p.AllEdgesColoured B :=
      p.allEdgesColoured_of_weight_lt_diameter
        B hB hD hShortD
    have hSubset : ∀ z : V,
        z ∈ p.support → z ∈ S := by
      intro z hz
      exact hz
    have hEdges : p.EdgesPreserved C M.toNatMetric F :=
      p.edgesPreserved_of_coloured_and_localRelationMap
        B hB hD M.toNatMetric F S
          (by
            intro e a b ha hb he
            exact hOldRel e a b ha hb he)
        hColours hSubset
    have hEnd :
        M.dist (F x) (F y) = C.cost x y := by
      calc
        M.dist (F x) (F y) = d.val + 1 :=
          hOldRel d x y hx hy hd
        _ = C.cost x y := hCost.symm
    have hBound :
        C.cost x y ≤ p.weight C :=
      p.endpoint_cost_le_weight_of_metric_certificate
        C M.toNatMetric F hEnd hEdges
    exact (Nat.not_lt.mpr hBound) hShort
  exact hShortest.trans hCost

end Bridge
end IntegerMetric
end AllThoseEPPA
