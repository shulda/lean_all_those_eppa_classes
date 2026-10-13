import AllThoseEPPA.Applications.KOrientations.CommonMoveRootRigidity
import AllThoseEPPA.Applications.KOrientations.GraphAutomorphismGroup

/-!
# Exact template root-set transfer for a moved canonical nonroot

If a single B₁ automorphism f moves the entire realized support W of
a canonical nonroot (x,W) into the distinguished source A₁, the
coordinates of W correspond bijectively to *all* the template roots
of g(x), where g = ι.lang⁻¹ * f.lang is the actual B₀ graph
automorphism. There are no extra template roots.

This is an exact support-to-root-set identity, not just inclusion,
and does not assume that B₀ globally has nonempty root sets. It is
a prerequisite for local correspondence on d-closed pieces.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The image in the template graph of the moved root-support
coordinates of p. Every element is witnessed by a genuine source
root t with f(w)=ι(t), not by a raw V-coordinate choice. -/
def MovedTemplateRoots
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B) : Set V :=
  {r | ∃ (w : W), w ∈ p.support ∧
    ∃ (t : RootsIn G k S), f w = ι t ∧ t.val = r}

/-- Under a common source move, the actual roots of the transformed
template centre are exactly the moved support coordinates. -/
theorem movedTemplateRoots_eq_roots
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B)
    (hMove : ∀ w ∈ p.support,
      ∃ t : RootsIn G k S, f w = ι t) :
    MovedTemplateRoots G k S B ι f p =
      G.roots k ((ι.lang⁻¹ * f.lang : G.graphAut).1 p.center) := by
  let g : G.graphAut := ι.lang⁻¹ * f.lang
  ext r
  constructor
  · rintro ⟨w, hw, t, hwt, rfl⟩
    obtain ⟨q, hq⟩ := RootMatches.exists_of_support p hw
    obtain ⟨s, hs, hsval⟩ :=
      rootMatches_alignment_under_move G k S B ι f p hMove hq
    have hts : t = s := ι.injective (hwt.symm.trans hs)
    have hqroot : q ∈ G.roots k p.center :=
      RootMatches.root_mem p hq
    rw [G.graphAut_roots_image k g p.center]
    refine ⟨q, hqroot, ?_⟩
    calc
      g.1 q = s.val := hsval.symm
      _ = t.val := congrArg Subtype.val hts.symm
  · intro hr
    rw [G.graphAut_roots_image k g p.center] at hr
    obtain ⟨q, hq, hqr⟩ := hr
    obtain ⟨w, hMatching⟩ := RootMatches.exists_of_root p hq
    obtain ⟨t, hwt, htval⟩ :=
      rootMatches_alignment_under_move
        G k S B ι f p hMove hMatching
    refine ⟨w, RootMatches.support_mem p hMatching, t, hwt, ?_⟩
    calc
      t.val = g.1 q := htval
      _ = r := hqr

end AllThoseEPPA.Applications.KOrientations
