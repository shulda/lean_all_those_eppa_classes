import AllThoseEPPA.Applications.KOrientations.OriginalDReconstructedEmbedding
import AllThoseEPPA.Applications.KOrientations.SourceSupportedEmbeddingVertexFormula
import AllThoseEPPA.Applications.KOrientations.SelectedOriginalRootGluing
import AllThoseEPPA.Applications.KOrientations.SelectedOriginalNonrootGluing

/-!
# ORIGINAL all-arity d(A) extension square for both actually chosen coherent EPPA selectors

The actual source embedding is the FULL original positive-arity set-valued
d-language embedding (not a unary reduct), obtained by composing the
first-stage trace isomorphism, the canonical supported-piece d-isomorphism
and inclusion in the fully reconstructed k-orientation witness.

Its pointwise vertex map is exactly the canonical choice-free source
reconstruction (not merely abstractly isomorphic). The genuinely selected
total reconstructed d-automorphism has separately Lean-audited gluing
equations on EVERY original root and EVERY original nonroot vertex in
the domain of any genuine all-arity d(A) partial automorphism.

Combining these gives precisely the public `Structure.ExtendsAlong`
predicate for the ACTUAL original embedding and selected FULL d-automorphism.
The language-action component is trivial on the final d-language;
the second auxiliary stage may retain a NONTRIVIAL Γ language component.
No false assumption on ambient d-closure of the first-stage old source
or global invariance of that source under the first chosen automorphism.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v w

/-- The actual all-arity original embedding has EXACTLY the canonical
root/nonroot reconstructed source vertex at EVERY original point,
including all components of its complete d-language map. -/
theorem firstStage_originalDReconstructedEmbedding_apply
    {V : Type u} {W : Type v} {X : Type w}
    [Fintype V] [Fintype W] [Fintype X]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (hBound : G.HasOutdegreeAtMost k)
    (hRooted : A.HasReachableRoots k)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (B : Structure (auxiliaryLanguage G k) X)
    (κ : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k (Set.range ι.toFun)) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) κ)
    (x : V) :
    firstStage_originalDReconstructedEmbedding
      A G k hBound hRooted ι B κ hFaith x =
    sourceReconstructedVertex G k (Set.range ι.toFun)
      (successorEmbedding_image_successorClosed A G ι)
      (successorEmbedding_image_rooted A G k hRooted ι)
      B κ ⟨ι x, ⟨x, rfl⟩⟩ := by
  let S : Set W := Set.range ι.toFun
  let hClosed := successorEmbedding_image_successorClosed A G ι
  let hSourceRooted := successorEmbedding_image_rooted A G k hRooted ι
  have hSource :
      (firstStageFullDSourceEmbedding A G k ι) x =
        (⟨ι x, ⟨x, rfl⟩⟩ : S) := by
    apply Subtype.ext
    rfl
  change
    ((faithful_sourceSupported_dTraceEmbedding
        G k S hBound hClosed hSourceRooted B κ hFaith)
      ((firstStageFullDSourceEmbedding A G k ι) x)).val =
      sourceReconstructedVertex G k S hClosed hSourceRooted
        B κ ⟨ι x, ⟨x, rfl⟩⟩
  rw [hSource]
  exact sourceSupportedPieceEquiv_val_eq_sourceReconstructedVertex
    G k S hClosed hSourceRooted B κ hFaith ⟨ι x, ⟨x, rfl⟩⟩

/-- The real selected total automorphism extends the ORIGINAL full
d(A) partial automorphism p along the genuine closed supported d(A)
embedding, in the PUBLIC EPPA API, on BOTH original root/nonroot sorts.
Every positive-arity set-valued F_n is retained in the underlying
Structure.Embedding and Structure.Automorphism types. -/
theorem firstStage_selectedReconstructedDAutomorphism_original_extendsAlong
    {V : Type u} {W : Type v} {X : Type w}
    [Fintype V] [Fintype W] [Fintype X]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (hBound : G.HasOutdegreeAtMost k)
    (hRooted : A.HasReachableRoots k)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (B : Structure (auxiliaryLanguage G k) X)
    (κ : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k (Set.range ι.toFun)) B)
    (t : Structure.CoherentExtension (auxiliaryAction G k) κ)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) κ)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k)) :
    Structure.ExtendsAlong dTrivialAction
      (firstStage_originalDReconstructedEmbedding
        A G k hBound hRooted ι B κ hFaith)
      p
      (firstStage_selectedReconstructedDAutomorphism
        A G k ι s B κ t hFaith p) := by
  constructor
  · exact Subsingleton.elim _ _
  · intro x hx
    rw [firstStage_originalDReconstructedEmbedding_apply
      A G k hBound hRooted ι B κ hFaith x,
      firstStage_originalDReconstructedEmbedding_apply
        A G k hBound hRooted ι B κ hFaith (p x)]
    by_cases hxRoot : A.IsRoot k x
    · exact
        firstStage_selectedReconstructedDAutomorphism_originalRoot_gluing
          A G k hRooted ι s B κ t hFaith p x hx hxRoot
    · exact
        firstStage_selectedReconstructedDAutomorphism_originalNonroot_gluing
          A G k hRooted ι s B κ t hFaith p x hx hxRoot

end AllThoseEPPA.Applications.KOrientations
