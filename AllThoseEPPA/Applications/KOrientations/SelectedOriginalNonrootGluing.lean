import AllThoseEPPA.Applications.KOrientations.SelectedSecondSourceRootSupportGluing
import AllThoseEPPA.Applications.KOrientations.SelectedReconstructedDAutomorphism
import AllThoseEPPA.Applications.KOrientations.SourceReconstructionVertex
import AllThoseEPPA.Applications.KOrientations.EmbeddedSuccessorSourceRooted
import AllThoseEPPA.Applications.KOrientations.SourceReconstructionNonroot

/-!
# Exact ORIGINAL nonroot d(A) extension square under the genuine selected automorphism

The actual canonical source copy in the choice-free reconstructed
witness maps a NONROOT old source point x∈S to a realized pair
  (κ.lang(x), κ '' fullRoots_B₀(x)).
There is NO arbitrary ordering or coset-representative coordinate:
the centre and COMPLETE root support uniquely determine the vertex.

For a genuine original all-arity d(A) partial automorphism p,
let g_p be the first chosen B₀ graph automorphism and f_p the
second chosen TOTAL auxiliary-language B₁ automorphism. The true
second selected ExtendsAlong group-component equation proves
  f_p.lang ∘ κ.lang = κ.lang ∘ g_p
and the first selected extension glues g_p(ι x)=ι(p x).
Thus the canonical nonroot CENTRE maps exactly correctly,
even when the auxiliary embedding κ has nonidentity Γ-label.

The independent full-root-support theorem proves f_p maps the
WHOLE κ-image of every root reachable from ι(x) exactly onto
the corresponding κ-image for ι(p x). Hence the nonroot
SUPPORT maps exactly, and the reconstructed nonroot vertices
are equal by their intrinsic centre/support uniqueness.

This is the actual ORIGINAL nonroot extension square in the
complete reconstructed d-language, not merely an abstract
B₀-graph coordinate equation. No g_p[S]=S, no ambient d-closure
of S, no arbitrary R_P label ordering. Combined with the
separate original-root extension square it will yield exact
extension on all old vertices. Full coherent EPPA theorem
remains a separate final assembly.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v w

/-- For ANY genuine original nonroot x in the source of the
original full d(A)-partial map p, the actually chosen
TOTAL reconstructed all-arity d-automorphism sends its exact
canonical source-copy image to the canonical image of p x.

The statement preserves the nonidentity language component
of the chosen auxiliary embedding and all root-support points. -/
theorem firstStage_selectedReconstructedDAutomorphism_originalNonroot_gluing
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
    (x : V) (hx : x ∈ p.source)
    (hxNonroot : ¬ A.IsRoot k x) :
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
  classical
  let S : Set W := Set.range ι.toFun
  let hClosed := successorEmbedding_image_successorClosed A G ι
  let hSourceRooted := successorEmbedding_image_rooted A G k hRooted ι
  let gp : G.graphAut := graphAutOfSuccessorAut G
    (s.extension (dPartialAutomorphism_to_successor A k p))
  let f := firstStage_selectedSecondAuxExtension A G k ι s B κ t p
  let α := firstStage_selectedAuxRootPartialAutomorphism A G k ι s p
  have hFirst : gp.1 (ι x) = ι (p x) :=
    (s.extension_spec (dPartialAutomorphism_to_successor A k p)).2 x hx
  have hOldNonroot : ¬ G.IsRoot k (ι x) := by
    intro h
    exact hxNonroot ((successorEmbedding_isRoot_iff A G k ι x).mp h)
  have hNewNonroot : ¬ G.IsRoot k (ι (p x)) := by
    intro h
    have hg : G.IsRoot k (gp.1 (ι x)) := by
      rw [hFirst]
      exact h
    exact hOldNonroot ((G.isRoot_iff_perm k gp.1 gp.2 (ι x)).mp hg)
  let old : CanonicalNonroot G k B :=
    (chosenSourceNonroot G k S hClosed hSourceRooted
      (ι x) ⟨x,rfl⟩ hOldNonroot).toCanonical B κ
  let new : CanonicalNonroot G k B :=
    (chosenSourceNonroot G k S hClosed hSourceRooted
      (ι (p x)) ⟨p x,rfl⟩ hNewNonroot).toCanonical B κ
  have hOldCenter : old.center = κ.lang.1 (ι x) :=
    (chosenSourceNonroot G k S hClosed hSourceRooted
      (ι x) ⟨x,rfl⟩ hOldNonroot).toCanonical_center B κ
  have hNewCenter : new.center = κ.lang.1 (ι (p x)) :=
    (chosenSourceNonroot G k S hClosed hSourceRooted
      (ι (p x)) ⟨p x,rfl⟩ hNewNonroot).toCanonical_center B κ
  have hGroup :
      f.lang.1 (κ.lang.1 (ι x)) =
        κ.lang.1 (gp.1 (ι x)) := by
    have hh := congrArg (fun a : G.graphAut => a.1 (ι x))
      (firstStage_selectedSecondAuxExtension_lang_gluing
        A G k ι s B κ t p)
    change f.lang.1 (κ.lang.1 (ι x)) =
        κ.lang.1 (α.lang.1 (ι x)) at hh
    exact hh
  have hCenter :
      (CanonicalNonroot.map f old).center = new.center := by
    calc
      (CanonicalNonroot.map f old).center =
        f.lang.1 old.center := rfl
      _ = f.lang.1 (κ.lang.1 (ι x)) :=
        congrArg f.lang.1 hOldCenter
      _ = κ.lang.1 (gp.1 (ι x)) := hGroup
      _ = κ.lang.1 (ι (p x)) :=
        congrArg κ.lang.1 hFirst
      _ = new.center := hNewCenter.symm
  have hOldSupport :
      old.support = κ.toFun ''
        {r : RootsIn G k S | r.val ∈ G.roots k (ι x)} :=
    (chosenSourceNonroot G k S hClosed hSourceRooted
      (ι x) ⟨x,rfl⟩ hOldNonroot).toCanonical_support_eq B κ
  have hNewSupport :
      new.support = κ.toFun ''
        {r : RootsIn G k S | r.val ∈ G.roots k (ι (p x))} :=
    (chosenSourceNonroot G k S hClosed hSourceRooted
      (ι (p x)) ⟨p x,rfl⟩ hNewNonroot).toCanonical_support_eq B κ
  have hSupport :
      (CanonicalNonroot.map f old).support = new.support := by
    change f '' old.support = new.support
    rw [hOldSupport, hNewSupport]
    exact firstStage_selectedSecondAuxExtension_originalRootSupport_image
      A G k ι s B κ t p x hx
  have hEqual : CanonicalNonroot.map f old = new :=
    CanonicalNonroot.eq_of_center_support _ _ hCenter hSupport
  have hSource :
      sourceReconstructedVertex G k S hClosed hSourceRooted B κ
        ⟨ι x, ⟨x,rfl⟩⟩ = Sum.inr old := by
    simp only [sourceReconstructedVertex, dif_neg hOldNonroot]
    rfl
  have hTarget :
      sourceReconstructedVertex G k S hClosed hSourceRooted B κ
        ⟨ι (p x), ⟨p x,rfl⟩⟩ = Sum.inr new := by
    simp only [sourceReconstructedVertex, dif_neg hNewNonroot]
    rfl
  calc
    firstStage_selectedReconstructedDAutomorphism
        A G k ι s B κ t hFaith p
        (sourceReconstructedVertex G k S hClosed hSourceRooted B κ
          ⟨ι x, ⟨x,rfl⟩⟩) =
      reconstructedVertexPerm G k B f (Sum.inr old) := by
        rw [hSource]
        exact firstStage_selectedReconstructedDAutomorphism_apply
          A G k ι s B κ t hFaith p (Sum.inr old)
    _ = Sum.inr (CanonicalNonroot.map f old) := rfl
    _ = Sum.inr new := congrArg Sum.inr hEqual
    _ = sourceReconstructedVertex G k S hClosed hSourceRooted B κ
        ⟨ι (p x), ⟨p x,rfl⟩⟩ := hTarget.symm

end AllThoseEPPA.Applications.KOrientations
