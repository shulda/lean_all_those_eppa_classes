import AllThoseEPPA.Examples.IntegerMetricPairModels
import AllThoseEPPA.Irreducible
import Mathlib.Tactic.FinCases

/-!
# Homomorphism-embeddings into a metric yield exact pair models

A general Γ-homomorphism-embedding is not necessarily injective
on the entire source and does not reflect relations globally.
Nevertheless, every realised relation tuple generates a closed
irreducible substructure. In the distance-colour language the
closure of an old binary distance edge contains both endpoints,
so the homomorphism-embedding reflects EVERY colour in BOTH
orientations of that pair.

This theorem packages this exact semantic consequence in the
pair-model API, and therefore derives symmetry, uniqueness and
loop-freeness whenever a partial source has a global metric
homomorphism-embedding completion. The local induced-pair
version used for the main EPPA transfer is the next target.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- The irreducible closure of an old labelled edge forces
all distance relations on that pair, in either orientation,
to be preserved and reflected by an arbitrary
homomorphism-embedding into a genuine metric. -/
private theorem exact_colours_on_edge
    {D : ℕ} {V W : Type u}
    (B : Structure (language D) V)
    (M : BoundedNatMetric D W)
    (f : Structure.Homomorphism (action D) B (toStructure M))
    (hf : Structure.Homomorphism.IsHomomorphismEmbedding (action D) f)
    (d : Fin D) (a b : V)
    (hd : B.rel (RelSymbol.edge d) ![a, b]) :
    (∀ e : Fin D,
      B.rel (RelSymbol.edge e) ![a, b] ↔
        M.dist (f a) (f b) = e.val + 1) ∧
    (∀ e : Fin D,
      B.rel (RelSymbol.edge e) ![b, a] ↔
        M.dist (f b) (f a) = e.val + 1) := by
  let xs : Fin 2 → V := ![a, b]
  let T : Set V := B.closureSet (Set.range xs)
  let hT : B.IsClosed T := B.isClosed_closureSet (Set.range xs)
  have hIrr : (B.induce T hT).IsIrreducible := by
    change (B.closureStructure (Set.range xs)).IsIrreducible
    exact B.relationTupleClosure_isIrreducible
      (RelSymbol.edge d) xs hd
  have ha : a ∈ T :=
    B.subset_closureSet (Set.range xs) ⟨0, rfl⟩
  have hb : b ∈ T :=
    B.subset_closureSet (Set.range xs) ⟨1, rfl⟩
  have hOn : Structure.Homomorphism.IsEmbeddingOn
      (action D) f T :=
    hf T hT hIrr
  have hExact (e : Fin D) (x y : V)
      (hx : x ∈ T) (hy : y ∈ T) :
      B.rel (RelSymbol.edge e) ![x, y] ↔
        M.dist (f x) (f y) = e.val + 1 := by
    have hTuple :
        ∀ i : Fin 2, (![x, y] : Fin 2 → V) i ∈ T := by
      intro i
      fin_cases i
      · exact hx
      · exact hy
    have hRel :=
      (hOn.2.1 (RelSymbol.edge e) ![x, y] hTuple).symm
    change B.rel (RelSymbol.edge e) ![x, y] ↔
      (toStructure M).rel (RelSymbol.edge e)
        (f.toFun ∘ ![x, y])
    simpa only [action_on_edge] using hRel
  exact ⟨fun e => hExact e a b ha hb,
    fun e => hExact e b a hb ha⟩

/-- Any homomorphism-embedding from an arbitrary partial
distance-coloured structure to a genuine D-metric produces
exact metric models for EVERY pair that bears an old colour
in at least one orientation. No global injectivity of f. -/
theorem exactPairModels_of_metricHomomorphismEmbedding
    {D : ℕ} {V W : Type u}
    (B : Structure (language D) V)
    (M : BoundedNatMetric D W)
    (f : Structure.Homomorphism (action D) B (toStructure M))
    (hf : Structure.Homomorphism.IsHomomorphismEmbedding (action D) f) :
    HasExactColouredPairModels B := by
  intro x y hLabel
  rcases hLabel with ⟨d, hForward | hReverse⟩
  · obtain ⟨hXY, hYX⟩ :=
      exact_colours_on_edge B M f hf d x y hForward
    exact ⟨W, M, f.toFun, hXY, hYX⟩
  · obtain ⟨hYX, hXY⟩ :=
      exact_colours_on_edge B M f hf d y x hReverse
    exact ⟨W, M, f.toFun, hXY, hYX⟩

/-- In particular, every partial colour structure admitting
a global homomorphism-embedding into a complete metric
automatically has valid canonical candidate costs. -/
theorem isConsistent_of_metricHomomorphismEmbedding
    {D : ℕ} {V W : Type u}
    (B : Structure (language D) V)
    (M : BoundedNatMetric D W)
    (f : Structure.Homomorphism (action D) B (toStructure M))
    (hf : Structure.Homomorphism.IsHomomorphismEmbedding (action D) f) :
    IsConsistentPartialMetric B :=
  isConsistentPartialMetric_of_exactPairModels B
    (exactPairModels_of_metricHomomorphismEmbedding B M f hf)

end Bridge
end IntegerMetric
end AllThoseEPPA
