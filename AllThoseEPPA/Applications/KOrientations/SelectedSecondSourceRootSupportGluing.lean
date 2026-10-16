import AllThoseEPPA.Applications.KOrientations.SelectedAuxRootDomainReachable
import AllThoseEPPA.Applications.KOrientations.SelectedFirstRootSetTransport
import AllThoseEPPA.Applications.KOrientations.SelectedSecondAuxRootGluing

/-!
# The actual selected second automorphism transports complete original root supports

In the full d(A)-language, a closed partial-map domain contains all
successors and, in particular, every reachable root of each original
domain point. The separately checked source-root-domain lemma
identifies EVERY root of B₀ reached from ι(x) with a point of the
actual selected auxiliary Γ-root partial-map domain.

The real second coherent extension f_p∈Aut(B₁) then genuinely
extends that partial map at EVERY such root; its root-coordinate
action is the ACTUAL chosen first graph automorphism g_p. The
latter maps the entire B₀ root set of ι(x) exactly onto that of
ι(p(x)), even though globally g_p[S]=S is NOT assumed.

Combining these three facts gives equality of the entire B₁
support sets
  f_p '' (κ '' Roots_B₀(ι x)) = κ '' Roots_B₀(ι(p x))
as sets of honest B₁ vertices, not merely an inclusion nor a
relation up to a choice of R_P tuple. This is the nonroot
support half of the final original d(A) extension square.
The canonical centre match and the final total-vertex
extension remain separately to prove.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v w

/-- Value of the genuinely selected Γ-root partial isomorphism
at ANY vertex of its EXACT closed source, as the ACTUAL
first-selected B₀ graph automorphism (not an arbitrary lift). -/
theorem firstStage_selectedAuxRootPartialAutomorphism_value
    {V : Type u} {W : Type v}
    [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (r : RootsIn G k (Set.range ι.toFun))
    (hr : r ∈ (firstStage_selectedAuxRootPartialAutomorphism A G k ι s p).source) :
    (firstStage_selectedAuxRootPartialAutomorphism A G k ι s p r).val =
      (graphAutOfSuccessorAut G
        (s.extension (dPartialAutomorphism_to_successor A k p))).1 r.val := by
  exact auxiliaryClosedRootPartialEquiv_value G k
    (Set.range ι.toFun)
    ((firstStageFullDSourceEmbedding A G k ι).toFun '' p.source)
    ((firstStageFullDSourceEmbedding A G k ι).toFun '' p.target)
    (graphAutOfSuccessorAut G
      (s.extension (dPartialAutomorphism_to_successor A k p)))
    (firstStage_selectedGraphAut_dTraceDomainImage A G k ι s p)
    r hr

/-- The chosen TOTAL second-stage B₁ automorphism sends the
entire genuine B₁-image of the root support of ι(x) to the
entire B₁-image of that of ι(p x), for every ORIGINAL full-d
partial-map domain point x, not just for original roots. -/
theorem firstStage_selectedSecondAuxExtension_originalRootSupport_image
    {V : Type u} {W : Type v} {X : Type w}
    [Fintype V] [Fintype W] [Fintype X]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (B : Structure (auxiliaryLanguage G k) X)
    (κ : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k (Set.range ι.toFun)) B)
    (t : Structure.CoherentExtension (auxiliaryAction G k) κ)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (x : V) (hx : x ∈ p.source) :
    (firstStage_selectedSecondAuxExtension A G k ι s B κ t p) ''
      (κ.toFun '' {r : RootsIn G k (Set.range ι.toFun) |
        r.val ∈ G.roots k (ι x)}) =
      κ.toFun '' {r : RootsIn G k (Set.range ι.toFun) |
        r.val ∈ G.roots k (ι (p x))} := by
  let α := firstStage_selectedAuxRootPartialAutomorphism A G k ι s p
  let f := firstStage_selectedSecondAuxExtension A G k ι s B κ t p
  let g := graphAutOfSuccessorAut G
    (s.extension (dPartialAutomorphism_to_successor A k p))
  have hRoots : g.1 '' G.roots k (ι x) =
      G.roots k (ι (p x)) :=
    firstStage_selectedGraphAut_originalRootSet_image
      A G k ι s p x hx
  ext z
  constructor
  · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
    have hrDom : r ∈ α.source :=
      firstStage_selectedAuxRootDomain_contains_sourceRoots
        A G k ι s p x hx r hr
    have hF : f (κ r) = κ (α r) :=
      (firstStage_selectedSecondAuxExtension_extendsRoot
        A G k ι s B κ t p).2 r hrDom
    rw [hF]
    refine ⟨α r, ?_, rfl⟩
    have hValue : (α r).val = g.1 r.val :=
      firstStage_selectedAuxRootPartialAutomorphism_value
        A G k ι s p r hrDom
    rw [← hRoots]
    exact ⟨r.val, hr, hValue.symm⟩
  · rintro ⟨r, hr, rfl⟩
    have hImage : r.val ∈ g.1 '' G.roots k (ι x) := by
      rw [hRoots]
      exact hr
    obtain ⟨y, hy, hgy⟩ := hImage
    have hyOld : y ∈ Set.range ι.toFun :=
      successorEmbedding_image_successorClosed A G ι
        (ι x) y ⟨x,rfl⟩ hy.2
    let q : RootsIn G k (Set.range ι.toFun) :=
      ⟨y, ⟨hyOld, hy.1⟩⟩
    have hqDom : q ∈ α.source :=
      firstStage_selectedAuxRootDomain_contains_sourceRoots
        A G k ι s p x hx q hy
    have hValue : (α q).val = g.1 q.val :=
      firstStage_selectedAuxRootPartialAutomorphism_value
        A G k ι s p q hqDom
    have hEq : α q = r :=
      Subtype.ext (hValue.trans hgy)
    refine ⟨κ q, ⟨q, hy, rfl⟩, ?_⟩
    calc
      f (κ q) = κ (α q) :=
        (firstStage_selectedSecondAuxExtension_extendsRoot
          A G k ι s B κ t p).2 q hqDom
      _ = κ r := congrArg κ.toFun hEq

end AllThoseEPPA.Applications.KOrientations
