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
  -- Work with the three ACTUAL selected partial automorphisms.
  -- Only their real source/range sets and the selected group elements
  -- matter: their total functions outside the sources need not agree.
  let ap := firstStage_selectedAuxRootPartialAutomorphism A G k ι s p
  let aq := firstStage_selectedAuxRootPartialAutomorphism A G k ι s q
  let ar := firstStage_selectedAuxRootPartialAutomorphism A G k ι s r
  have hDom : ap.target = aq.source := by
    change auxiliaryClosedRootDomain G k S (E.toFun '' p.target) =
      auxiliaryClosedRootDomain G k S (E.toFun '' q.source)
    rw [hpq]
  refine ⟨hDom, ?_⟩
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · -- Actual selected language-group elements multiply coherently.
    change gr = gq * gp
    exact hGroup
  · -- The composite partial map has the original selected source.
    change auxiliaryClosedRootDomain G k S (E.toFun '' r.source) =
      auxiliaryClosedRootDomain G k S (E.toFun '' p.source)
    rw [hrSource]
  · -- The vertex action is the composition ON ITS SOURCE.
    intro x hx
    have hxR : x ∈ auxiliaryClosedRootDomain G k S (E.toFun '' r.source) := hx
    have hxP : x ∈ auxiliaryClosedRootDomain G k S (E.toFun '' p.source) := by
      simpa only [hrSource] using hxR
    have hpx : (ap x).val = gp.1 x.val :=
      auxiliaryClosedRootPartialEquiv_value
        G k S (E.toFun '' p.source) (E.toFun '' p.target)
        gp (firstStage_selectedGraphAut_dTraceDomainImage A G k ι s p)
        x hxP
    have hxQ : ap x ∈ auxiliaryClosedRootDomain G k S
        (E.toFun '' q.source) := by
      have hmap : ap x ∈ aq.source := by
        rw [← hDom]
        exact ap.map_source hxP
      exact hmap
    have hqx : (aq (ap x)).val = gq.1 (ap x).val :=
      auxiliaryClosedRootPartialEquiv_value
        G k S (E.toFun '' q.source) (E.toFun '' q.target)
        gq (firstStage_selectedGraphAut_dTraceDomainImage A G k ι s q)
        (ap x) hxQ
    have hrx : (ar x).val = gr.1 x.val :=
      auxiliaryClosedRootPartialEquiv_value
        G k S (E.toFun '' r.source) (E.toFun '' r.target)
        gr (firstStage_selectedGraphAut_dTraceDomainImage A G k ι s r)
        x hxR
    apply Subtype.ext
    change (ar x).val = (aq (ap x)).val
    calc
      (ar x).val = gr.1 x.val := hrx
      _ = (gq * gp).1 x.val :=
        congrArg (fun h : G.graphAut => h.1 x.val) hGroup
      _ = gq.1 (gp.1 x.val) := by simp
      _ = gq.1 (ap x).val := congrArg gq.1 hpx.symm
      _ = (aq (ap x)).val := hqx.symm

end AllThoseEPPA.Applications.KOrientations
