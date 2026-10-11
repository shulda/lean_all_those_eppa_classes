import AllThoseEPPA.Examples.IntegerMetricParallelEmbeddings
import AllThoseEPPA.Examples.IntegerMetricIsometriesToEmbeddings
import AllThoseEPPA.StrongCompletionTreeAmalgamationClass

/-!
# Finite metric amalgamation gives the paper's EXACT class interface

The mathematical gluing input is deliberately stated in ordinary
metric language: two finite bounded integer metric spaces, two
injective maps from one (not necessarily metrically named) common
source, and equality of their pulled-back distances. It requires
two isometric extensions into one finite bounded integer metric,
with the two embeddings agreeing on the interface.

From this purely metric amalgamation law, construct the manuscript's
genuine FiniteAmalgamationClass for the complete binary
distance-colour relational encodings. The common relational
structure Q is NOT assumed to be a metric encoding: exact embeddings
into the two full encodings supply the common distances automatically.

The amalgamation law is a PROP-valued premise here, NOT an axiom or
an assertion that every D satisfies it. The remaining GlueSpace
construction is intended to discharge the premise.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- The finite D-bounded integer metric amalgamation assertion,
with exact compatibility of the two maps on a common source.
The interface I itself need not come with a metric structure. -/
def HasFiniteMetricAmalgamation (D : ℕ) : Prop :=
  ∀ {I X Y : Type u} [Finite X] [Finite Y]
    (MX : BoundedNatMetric D X)
    (MY : BoundedNatMetric D Y)
    (f : I ↪ X) (g : I ↪ Y),
    (∀ i j : I,
      MX.dist (f i) (f j) = MY.dist (g i) (g j)) →
    ∃ (W : Type u) (_ : Finite W)
      (MW : BoundedNatMetric D W)
      (jX : X → W) (jY : Y → W),
      (∀ x y : X, MW.dist (jX x) (jX y) = MX.dist x y) ∧
      (∀ x y : Y, MW.dist (jY x) (jY y) = MY.dist x y) ∧
      (∀ i : I, jX (f i) = jY (g i))

/-- Embeddings into a full metric encoding are determined by their
point maps, since the distance-colour action group is PUnit.
There is no hidden choice of a nontrivial language relabelling. -/
theorem metricEncodingEmbedding_ext_of_apply
    {D : ℕ} {I V : Type u}
    (Q : Structure (language D) I)
    (MV : BoundedNatMetric D V)
    (e₁ e₂ : Structure.Embedding (action D) Q (toStructure MV))
    (h : ∀ i : I, e₁ i = e₂ i) : e₁ = e₂ := by
  cases e₁ with
  | mk l₁ f₁ hInject₁ hRel₁ hFunc₁ =>
    cases e₂ with
    | mk l₂ f₂ hInject₂ hRel₂ hFunc₂ =>
      have hl : l₁ = l₂ := Subsingleton.elim _ _
      cases hl
      have hf : f₁ = f₂ := by
        funext i
        exact h i
      cases hf
      rfl

/-- Every finite ordinary D-metric amalgamation operation supplies
the exact paper-level amalgamation class of complete encodings.
The source Q of a requested amalgam is allowed to be an arbitrary
partial relation structure; no extra metric assumption on Q. -/
noncomputable def finiteMetricEncodingAmalgamationClass
    (D : ℕ)
    (hAmalgam : HasFiniteMetricAmalgamation.{u} D) :
    TreeLike.FiniteAmalgamationClass (action D) where
  mem := fun {V} C =>
    ∃ (hV : Finite V) (M : BoundedNatMetric D V),
      C = toStructure M
  amalgamate := by
    intro I X Y Q B₁ B₂ f g hB₁ hB₂
    obtain ⟨hFiniteX, MX, hMX⟩ := hB₁
    obtain ⟨hFiniteY, MY, hMY⟩ := hB₂
    subst B₁
    subst B₂
    letI : Finite X := hFiniteX
    letI : Finite Y := hFiniteY
    have hShared : ∀ i j : I,
        MX.dist (f i) (f j) = MY.dist (g i) (g j) :=
      parallelMetricEmbeddings_dist_agree Q MX MY f g
    let φ : I ↪ X := ⟨f.toFun, f.injective⟩
    let ψ : I ↪ Y := ⟨g.toFun, g.injective⟩
    obtain ⟨W, hFiniteW, MW, jX, jY, hJX, hJY, hAgree⟩ :=
      hAmalgam MX MY φ ψ hShared
    let eX : Structure.Embedding (action D)
        (toStructure MX) (toStructure MW) :=
      encodingEmbeddingOfDistancePreserving MX MW jX hJX
    let eY : Structure.Embedding (action D)
        (toStructure MY) (toStructure MW) :=
      encodingEmbeddingOfDistancePreserving MY MW jY hJY
    refine ⟨W, hFiniteW, toStructure MW,
      ⟨hFiniteW, MW, rfl⟩, eX, eY, ?_⟩
    apply metricEncodingEmbedding_ext_of_apply Q MW
    intro i
    change jX (f i) = jY (g i)
    exact hAgree i

/-- Semantic membership in the exact metric encoding class. -/
theorem finiteMetricEncodingAmalgamationClass_members_are_metrics
    {D : ℕ} (hAmalgam : HasFiniteMetricAmalgamation.{u} D)
    {V : Type u} (C : Structure (language D) V)
    (hC : (finiteMetricEncodingAmalgamationClass D hAmalgam).mem C) :
    ∃ (M : BoundedNatMetric D V), C = toStructure M := by
  obtain ⟨_, M, hM⟩ := hC
  exact ⟨M, hM⟩

/-- Any concrete finite D-metric is a member of the class. -/
theorem finiteMetricEncodingAmalgamationClass_mem
    {D : ℕ} (hAmalgam : HasFiniteMetricAmalgamation.{u} D)
    {V : Type u} [Finite V]
    (M : BoundedNatMetric D V) :
    (finiteMetricEncodingAmalgamationClass D hAmalgam).mem
      (toStructure M) := by
  exact ⟨inferInstance, M, rfl⟩

end Bridge
end IntegerMetric
end AllThoseEPPA
