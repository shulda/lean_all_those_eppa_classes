import AllThoseEPPA.Applications.KOrientations.SelectedSecondAuxRootGluing
import AllThoseEPPA.Applications.KOrientations.SelectedReconstructedDAutomorphism
import AllThoseEPPA.Applications.KOrientations.EmbeddedSuccessorSourceRooted
import AllThoseEPPA.Applications.KOrientations.SourceReconstructionVertex
import AllThoseEPPA.Applications.KOrientations.AuxiliaryClosedRootUnaryExactImage

/-!
# Exact original d(A) root gluing for the genuinely chosen reconstructed automorphism

The ORIGINAL full d(A) source carries genuine arbitrary-arity set-valued
root functions. Its first successor embedding ι:A→B₀ has an old-image
S that is successor-closed and (when A is rooted) itself rooted,
although S need not be ambient d-closed in B₀.

For an original root x of A, construct its actual embedded root
rx∈RootsIn(B₀,k,S), keeping the canonical group-valued second
embedding κ and its possible nontrivial language component.

If x lies in the real source domain of an arbitrary original
full-d partial automorphism p, rx belongs to the exact selected
Γ-root partial source domain of the SECOND EPPA selector. Its
image there has ambient B₀ coordinate ι(p x), not just a related
template point. The selected TOTAL B₁ automorphism therefore
maps κ(rx) precisely to κ(ι(p x)), and the selected TOTAL full-d
reconstructed automorphism does the same on the original
reconstructed source-copy ROOT vertices.

This is the original-root half of the final extension square.
The nonroot half and assembled faithful coherent EPPA theorem
remain separate; no global g[S]=S or source ambient d-closure.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v w

/-- Canonical original root as a TRUE point of the selected
first-stage auxiliary source root sort. -/
def originalRootInFirstAux
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (x : V) (hxRoot : A.IsRoot k x) :
    RootsIn G k (Set.range ι.toFun) :=
  ⟨ι x, ⟨⟨x, rfl⟩,
    (successorEmbedding_isRoot_iff A G k ι x).2 hxRoot⟩⟩

/-- Every genuine original partial-map root lies in the EXACT
closed Γ-root domain of the selected second-stage partial map. -/
theorem originalRootInFirstAux_mem_selectedSource
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (x : V) (hx : x ∈ p.source) (hxRoot : A.IsRoot k x) :
    originalRootInFirstAux A G k ι x hxRoot ∈
      (firstStage_selectedAuxRootPartialAutomorphism
        A G k ι s p).source := by
  change
    (⟨ι x, ⟨x, rfl⟩⟩ : Set.range ι.toFun) ∈
      (firstStageFullDSourceEmbedding A G k ι).toFun '' p.source
  refine ⟨x, hx, ?_⟩
  apply Subtype.ext
  rfl

/-- At every actual original full-d domain root, the
first-selected Γ-root PARTIAL automorphism is exactly the
old original map p, embedded by ι on the underlying B₀
vertex coordinate; the value identity is checked through
the real first coherent selector and its ExtendsAlong law. -/
theorem originalRootInFirstAux_selectedImage_val
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (x : V) (hx : x ∈ p.source) (hxRoot : A.IsRoot k x) :
    (firstStage_selectedAuxRootPartialAutomorphism
      A G k ι s p
      (originalRootInFirstAux A G k ι x hxRoot)).val =
      ι (p x) := by
  let rx := originalRootInFirstAux A G k ι x hxRoot
  have hMem :=
    originalRootInFirstAux_mem_selectedSource A G k ι s p x hx hxRoot
  have hMap : (firstStage_selectedAuxRootPartialAutomorphism
      A G k ι s p rx).val =
      (graphAutOfSuccessorAut G
        (s.extension (dPartialAutomorphism_to_successor A k p))).1 rx.val := by
    exact auxiliaryClosedRootPartialEquiv_value G k
      (Set.range ι.toFun)
      ((firstStageFullDSourceEmbedding A G k ι).toFun '' p.source)
      ((firstStageFullDSourceEmbedding A G k ι).toFun '' p.target)
      (graphAutOfSuccessorAut G
        (s.extension (dPartialAutomorphism_to_successor A k p)))
      (firstStage_selectedGraphAut_dTraceDomainImage A G k ι s p)
      rx hMem
  have hFirst : (s.extension
      (dPartialAutomorphism_to_successor A k p)) (ι x) = ι (p x) :=
    (s.extension_spec (dPartialAutomorphism_to_successor A k p)).2 x hx
  calc
    (firstStage_selectedAuxRootPartialAutomorphism
        A G k ι s p rx).val =
      (graphAutOfSuccessorAut G
        (s.extension (dPartialAutomorphism_to_successor A k p))).1 rx.val := hMap
    _ = (s.extension (dPartialAutomorphism_to_successor A k p)) (ι x) := rfl
    _ = ι (p x) := hFirst

/-- **True ORIGINAL ROOT gluing**: the actually chosen TOTAL
full-d automorphism of the whole reconstructed witness extends
the original d(A) partial automorphism at every source root x.
This equation uses the real source-copy embedding with the
possibly NONIDENTITY auxiliary embedding-language component. -/
theorem firstStage_selectedReconstructedDAutomorphism_originalRoot_gluing
    {V : Type u} {W : Type v} {X : Type w}
    [Fintype V] [Fintype W] [Fintype X]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
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
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (x : V) (hx : x ∈ p.source) (hxRoot : A.IsRoot k x) :
    firstStage_selectedReconstructedDAutomorphism
      A G k ι s B κ t hFaith p
      (sourceReconstructedVertex G k (Set.range ι.toFun)
        (successorEmbedding_image_successorClosed A G ι)
        (successorEmbedding_image_rooted A G k hRooted ι)
        B κ ⟨ι x, ⟨x, rfl⟩⟩) =
    sourceReconstructedVertex G k (Set.range ι.toFun)
      (successorEmbedding_image_successorClosed A G ι)
      (successorEmbedding_image_rooted A G k hRooted ι)
      B κ ⟨ι (p x), ⟨p x, rfl⟩⟩ := by
  let rx := originalRootInFirstAux A G k ι x hxRoot
  let α := firstStage_selectedAuxRootPartialAutomorphism A G k ι s p
  have hMem : rx ∈ α.source :=
    originalRootInFirstAux_mem_selectedSource A G k ι s p x hx hxRoot
  have hValue : (α rx).val = ι (p x) :=
    originalRootInFirstAux_selectedImage_val A G k ι s p x hx hxRoot
  have hOldRoot : G.IsRoot k (ι x) :=
    (successorEmbedding_isRoot_iff A G k ι x).2 hxRoot
  have hTargetRoot : G.IsRoot k (ι (p x)) := by
    rw [← hValue]
    exact (α rx).property.2
  have hEqRoot :
      α rx =
        (⟨ι (p x), ⟨⟨p x,rfl⟩,hTargetRoot⟩⟩ :
          RootsIn G k (Set.range ι.toFun)) :=
    Subtype.ext hValue
  let f := firstStage_selectedSecondAuxExtension A G k ι s B κ t p
  let hClosed := successorEmbedding_image_successorClosed A G ι
  let hSourceRooted := successorEmbedding_image_rooted A G k hRooted ι
  calc
    firstStage_selectedReconstructedDAutomorphism
        A G k ι s B κ t hFaith p
        (sourceReconstructedVertex G k (Set.range ι.toFun)
          hClosed hSourceRooted B κ ⟨ι x, ⟨x,rfl⟩⟩) =
      reconstructedVertexPerm G k B f (Sum.inl (κ rx)) := by
        rw [firstStage_selectedReconstructedDAutomorphism_apply]
        simp only [sourceReconstructedVertex, dif_pos hOldRoot]
        rfl
    _ = Sum.inl (κ (α rx)) :=
      firstStage_selectedSecondAuxExtension_root_gluing
        A G k ι s B κ t p rx hMem
    _ = Sum.inl (κ
        (⟨ι (p x), ⟨⟨p x,rfl⟩,hTargetRoot⟩⟩ :
          RootsIn G k (Set.range ι.toFun))) := by
        rw [hEqRoot]
    _ = sourceReconstructedVertex G k (Set.range ι.toFun)
        hClosed hSourceRooted B κ ⟨ι (p x), ⟨p x, rfl⟩⟩ := by
          simp only [sourceReconstructedVertex, dif_pos hTargetRoot]
          rfl

end AllThoseEPPA.Applications.KOrientations
