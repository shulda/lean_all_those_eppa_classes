import AllThoseEPPA.Applications.KOrientations.FirstStageSelectedAuxRootEquivalence
import AllThoseEPPA.Applications.KOrientations.AuxiliaryClosedRootCompositeImage
import AllThoseEPPA.Applications.KOrientations.FirstStageSelectedGraphCoherence

/-!
# Ordered coherent triples of ACTUAL first-to-second k-orientation Γ-root maps

The original source is the genuine full arity-indexed d(A) with
set-valued F_n. For each original d-partial automorphism p, the FIRST
coherent selector yields a REAL graph automorphism g_p∈Aut(B₀), whose
restriction to the intrinsically closed d-trace image of p.source
induces the exact auxiliary Γ-root partial automorphism a_p used
by the SECOND selector.

For an original public coherent triple (p,q,r), its true closed
partial domains satisfy p.target=q.source, r.source=p.source and
r.target=q.target; and the already certified first selector obeys
g_r=g_q*g_p IN THE CORRECT ORDER. Real graph automorphism image
equalities show g_p maps T₁ onto T₂ and g_q maps T₂ onto T₃, while
the generic auxiliary-root composition theorem yields a genuine
coherent triple (a_p,a_q,a_(g_q*g_p)).

The third actual selected root map a_r is mathematically equivalent
to this canonical composite map: its exact closed source/range
sets agree and its graph group component is g_q*g_p. We combine
these statements without assuming a global g[S]=S, ambient
d-closed S or equality of irrelevant PartialEquiv values
outside their sources.

This is a candidate interface for coherence of the SECOND selector;
one must still prove subsequent extension on the reconstructed
full d-structure, exact gluing on original d(A), and faithful
coherent thm:DF for k-orientations.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every original full-d coherent triple induces a genuine
ordered coherent triple of its *actual first-selected* input
Γ-root partial automorphisms for the second faithful coherent
EPPA witness. All internal d-trace closure domains and full
Aut(B₀) language-group components are retained. -/
theorem firstStage_selectedAuxRootPartialAutomorphism_coherentTriple
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (p q r : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (hTriple : Structure.PartialIsomorphism.CoherentTriple p q r) :
    Structure.PartialIsomorphism.CoherentTriple
      (firstStage_selectedAuxRootPartialAutomorphism A G k ι s p)
      (firstStage_selectedAuxRootPartialAutomorphism A G k ι s q)
      (firstStage_selectedAuxRootPartialAutomorphism A G k ι s r) := by
  obtain ⟨hpq, hReq⟩ := hTriple
  let S : Set W := Set.range ι.toFun
  let E := firstStageFullDSourceEmbedding A G k ι
  let T₁ := E.toFun '' p.source
  let T₂ := E.toFun '' p.target
  let T₃ := E.toFun '' q.target
  let gp : G.graphAut := graphAutOfSuccessorAut G
    (s.extension (dPartialAutomorphism_to_successor A k p))
  let gq : G.graphAut := graphAutOfSuccessorAut G
    (s.extension (dPartialAutomorphism_to_successor A k q))
  let gr : G.graphAut := graphAutOfSuccessorAut G
    (s.extension (dPartialAutomorphism_to_successor A k r))
  have hrSource : r.source = p.source := by
    calc
      r.source = (q.comp p hpq).source :=
        PartialEquiv.EqOnSource.source_eq hReq.2
      _ = p.source := rfl
  have hrTarget : r.target = q.target := by
    calc
      r.target = (q.comp p hpq).target :=
        PartialEquiv.EqOnSource.target_eq hReq.2
      _ = q.target := rfl
  have hGroup : gr = gq * gp :=
    firstStage_coherentSelector_graphAut_coherentTriple
      A G k ι s p q r ⟨hpq, hReq⟩
  have hClosed1 : (dTraceStructure G k S).IsClosed T₁ :=
    firstStage_dPartialSourceTrace_isClosed A G k ι p
  have hClosed2 : (dTraceStructure G k S).IsClosed T₂ :=
    firstStage_dPartialTargetTrace_isClosed A G k ι p
  have hClosed3 : (dTraceStructure G k S).IsClosed T₃ :=
    firstStage_dPartialTargetTrace_isClosed A G k ι q
  have hpImage : gp.1 '' (Subtype.val '' T₁) =
      Subtype.val '' T₂ :=
    firstStage_selectedGraphAut_dTraceDomainImage A G k ι s p
  have hqImage : gq.1 '' (Subtype.val '' T₂) =
      Subtype.val '' T₃ := by
    have h := firstStage_selectedGraphAut_dTraceDomainImage
      A G k ι s q
    change gq.1 '' (Subtype.val '' (E.toFun '' q.source)) =
      Subtype.val '' T₃ at h
    change gq.1 '' (Subtype.val '' (E.toFun '' p.target)) =
      Subtype.val '' T₃
    rw [hpq]
    exact h
  have hCombined : (gq * gp).1 '' (Subtype.val '' T₁) =
      Subtype.val '' T₃ :=
    auxiliaryClosedRootDomain_image_comp G S T₁ T₂ T₃
      gp gq hpImage hqImage
  let a₁ := auxiliaryClosedRootPartialIsomorphism
    G k S T₁ T₂ hClosed1 hClosed2 gp hpImage
  let a₂ := auxiliaryClosedRootPartialIsomorphism
    G k S T₂ T₃ hClosed2 hClosed3 gq hqImage
  let a₃ := auxiliaryClosedRootPartialIsomorphism
    G k S T₁ T₃ hClosed1 hClosed3 (gq * gp) hCombined
  have hGeneric : Structure.PartialIsomorphism.CoherentTriple
      a₁ a₂ a₃ :=
    auxiliaryClosedRootPartialIsomorphism_coherentTriple_of_images
      G k S T₁ T₂ T₃ hClosed1 hClosed2 hClosed3
      gp gq hpImage hqImage
  have ha₁ : a₁ =
      firstStage_selectedAuxRootPartialAutomorphism A G k ι s p := rfl
  have ha₂ : a₂ =
      firstStage_selectedAuxRootPartialAutomorphism A G k ι s q := by
    dsimp only [a₂, T₂]
    rw [hpq]
    rfl
  have hImageR : gr.1 '' (Subtype.val '' (E.toFun '' r.source)) =
      Subtype.val '' (E.toFun '' r.target) :=
    firstStage_selectedGraphAut_dTraceDomainImage A G k ι s r
  have hThird : Structure.PartialIsomorphism.Equivalent
      (firstStage_selectedAuxRootPartialAutomorphism A G k ι s r)
      a₃ := by
    apply auxiliaryClosedRootPartialIsomorphism_equivalent_of_equal_data
      G k S
      (E.toFun '' r.source) (E.toFun '' r.target)
      T₁ T₃
      (firstStage_dPartialSourceTrace_isClosed A G k ι r)
      (firstStage_dPartialTargetTrace_isClosed A G k ι r)
      hClosed1 hClosed3 gr (gq * gp)
      hImageR hCombined
    · exact congrArg (fun T : Set V => E.toFun '' T) hrSource
    · exact congrArg (fun T : Set V => E.toFun '' T) hrTarget
    · exact hGroup
  rw [ha₁, ha₂] at hGeneric
  obtain ⟨hDom, hComposed⟩ := hGeneric
  refine ⟨hDom, ?_⟩
  exact ⟨hThird.1.trans hComposed.1,
    Setoid.trans hThird.2 hComposed.2⟩

end AllThoseEPPA.Applications.KOrientations
