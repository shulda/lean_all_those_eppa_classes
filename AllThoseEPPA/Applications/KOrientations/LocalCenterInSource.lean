import AllThoseEPPA.Applications.KOrientations.CommonMoveRootRigidity
import AllThoseEPPA.Automorphism

/-!
# The transformed centre of a locally moved nonroot belongs to S

A canonical nonroot p=(x,W) comes from a realized R_P relation.
If one B₁ automorphism f sends ALL of W into the source root sort,
the entire realized tuple is moved into the embedded A₁.
Exact relation reflection forces the transformed label R_(gP)
to be realized in A₁, hence forces its centre g(x) to be an
actual vertex of the original successor-closed template source S.

It would be incorrect to deduce this merely from the roots of
g(x) lying in S: the label R_P is essential here.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

theorem canonicalNonroot_commonMove_center_in_source
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B)
    (hMove : ∀ w ∈ p.support,
      ∃ t : RootsIn G k S, f w = ι t) :
    (ι.lang⁻¹*f.lang : G.graphAut).1 p.center ∈ S := by
  classical
  obtain ⟨n,P,xs,hc,hRel,hU⟩ := p.witnessed
  have hPart (i : Fin n) :
      ∃ t : RootsIn G k S, f (xs i) = ι t := by
    apply hMove
    rw [← hU]
    exact ⟨i,rfl⟩
  let ts : Fin n → RootsIn G k S :=
    fun i => Classical.choose (hPart i)
  have hPts : ∀ i : Fin n, f (xs i) = ι (ts i) :=
    fun i => Classical.choose_spec (hPart i)
  let g : G.graphAut := ι.lang⁻¹*f.lang
  have hLabel :
      (auxiliaryAction G k).onRel ι.lang
        (AuxiliaryRel.root (RootPattern.transportAut g P)) =
      (auxiliaryAction G k).onRel f.lang (AuxiliaryRel.root P) := by
    change AuxiliaryRel.root
      (RootPattern.transportAut ι.lang
        (RootPattern.transportAut (ι.lang⁻¹*f.lang) P)) =
      AuxiliaryRel.root (RootPattern.transportAut f.lang P)
    rw [← RootPattern.transportAut_mul]
    simp [← mul_assoc]
  have hMap : B.rel
      ((auxiliaryAction G k).onRel f.lang (AuxiliaryRel.root P))
      (f ∘ xs) :=
    (Structure.Automorphism.map_rel_iff
      f (AuxiliaryRel.root P) xs).2 hRel
  have hTuple : (f ∘ xs) = (ι.toFun ∘ ts) := by
    funext i
    exact hPts i
  have hSource :
      (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.root (RootPattern.transportAut g P)) ts := by
    apply (ι.map_rel_iff
      (AuxiliaryRel.root (RootPattern.transportAut g P)) ts).1
    rw [hLabel, ← hTuple]
    exact hMap
  have hCentre : g.1 P.center ∈ S :=
    ((auxiliaryRootStructure_root G k n S
      (RootPattern.transportAut g P) ts).mp hSource).1
  simpa only [hc] using hCentre

end AllThoseEPPA.Applications.KOrientations
