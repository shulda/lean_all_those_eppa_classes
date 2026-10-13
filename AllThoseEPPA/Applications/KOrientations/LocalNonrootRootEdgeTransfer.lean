import AllThoseEPPA.Applications.KOrientations.CommonMoveRootRigidity
import AllThoseEPPA.Applications.KOrientations.ReconstructionEdges

/-!
# Local edge reflection from a canonical nonroot to a B₁ root

Suppose an auxiliary automorphism f moves a root vertex a and the
complete support W of a canonical nonroot p=(x,W) into the original
root-only source. Then the outgoing edge p→a is equivalent to the
template edge g(x)→t, where f(a)=ι(t) and
g=ι.lang⁻¹*f.lang is the actual B₀ graph automorphism.

The proof uses the *whole* canonical root correspondence; the
backward direction must recover the precise B₁ coordinate a,
rather than merely some root with a suitable template label.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

theorem local_nonroot_root_edge_iff
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B)
    (hp : ∀ w ∈ p.support,
      ∃ s : RootsIn G k S, f w = ι s)
    (a : W) (t : RootsIn G k S)
    (ha : f a = ι t) :
    ReconstructedEdge G k B (.inr p) (.inl a) ↔
      G.edge ((ι.lang⁻¹*f.lang : G.graphAut).1 p.center) t.val := by
  let g : G.graphAut := ι.lang⁻¹*f.lang
  constructor
  · rintro ⟨r,hEdge,hMatch⟩
    obtain ⟨s,hs,hsv⟩ :=
      rootMatches_alignment_under_move
        G k S B ι f p hp hMatch
    have hst : s = t := ι.injective (hs.symm.trans ha)
    have hImage : g.1 r = t.val := by
      calc
        g.1 r = s.val := hsv.symm
        _ = t.val := congrArg Subtype.val hst
    have hTransport : G.edge (g.1 p.center) (g.1 r) :=
      (g.2 p.center r).2 hEdge
    rw [hImage] at hTransport
    exact hTransport
  · intro hTemplate
    let r : V := g.1.symm t.val
    have hgr : g.1 r = t.val :=
      g.1.apply_symm_apply t.val
    have hRootR : G.IsRoot k r := by
      apply (G.graphAut_root_iff k g r).mp
      simpa only [hgr] using t.property.2
    have hEdgeR : G.edge p.center r :=
      (g.2 p.center r).1 (by simpa only [hgr] using hTemplate)
    have hRootSet : r ∈ G.roots k p.center :=
      ⟨hRootR, G.reaches_of_edge hEdgeR⟩
    obtain ⟨w,hMatch⟩ := RootMatches.exists_of_root p hRootSet
    obtain ⟨s,hs,hsv⟩ :=
      rootMatches_alignment_under_move
        G k S B ι f p hp hMatch
    have hst : s = t := by
      apply Subtype.ext
      calc
        s.val = g.1 r := hsv
        _ = t.val := hgr
    have hwa : w = a := by
      apply f.toEquiv.injective
      calc
        f w = ι s := hs
        _ = ι t := congrArg ι hst
        _ = f a := ha.symm
    refine ⟨r,hEdgeR,?_⟩
    simpa only [hwa] using hMatch

end AllThoseEPPA.Applications.KOrientations
