import AllThoseEPPA.Applications.KOrientations.ReconstructionNestedNeighbourRigidity
import AllThoseEPPA.Applications.KOrientations.RootMatchingRelation
import AllThoseEPPA.Automorphism

/-!
# Coordinate rigidity under a common source-moving automorphism

The existing nested-support rigidity theorem works only when both
realized root sets are included in one *realized R_P tuple*. For the
outneighbourhood of a B₁-root a, its whole unary closure need not be
the support of a realized non-root label.

The correct replacement is to fix an automorphism f moving that
entire closure into the original root-only source. Each R_P tuple
whose support is moved by f then has coordinates aligned with its
template roots by the same B₀ automorphism ι.lang⁻¹ * f.lang.

Consequently two canonical non-root vertices with the same template
centre, whose supports are both moved into the source by this *one*
automorphism, must have identical supports. This will give the
injectivity of the non-root fibres in the root-outdegree proof.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every intrinsic root match r↔w in a realized non-root p,
under a fixed common source-moving automorphism f, sends w to the
embedded image of the corresponding transformed template root. -/
theorem rootMatches_alignment_under_move
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B)
    (hMove : ∀ w ∈ p.support,
      ∃ t : RootsIn G k S, f w = ι t)
    {r : V} {w : W}
    (hMatch : RootMatches G k B p r w) :
    ∃ t : RootsIn G k S,
      f w = ι t ∧ t.val = (ι.lang⁻¹ * f.lang : G.graphAut).1 r := by
  classical
  obtain ⟨n, P, xs, i, _, hR, hW, hr, hw⟩ := hMatch
  have hPart (j : Fin n) :
      ∃ t : RootsIn G k S, f (xs j) = ι t := by
    apply hMove
    rw [← hW]
    exact ⟨j, rfl⟩
  let ts : Fin n → RootsIn G k S :=
    fun j => Classical.choose (hPart j)
  have hPoints : ∀ j : Fin n, f (xs j) = ι (ts j) :=
    fun j => Classical.choose_spec (hPart j)
  let g : G.graphAut := ι.lang⁻¹ * f.lang
  have hLabel :
      (auxiliaryAction G k).onRel ι.lang
        (AuxiliaryRel.root (RootPattern.transportAut g P)) =
      (auxiliaryAction G k).onRel f.lang (AuxiliaryRel.root P) := by
    change AuxiliaryRel.root
      (RootPattern.transportAut ι.lang
        (RootPattern.transportAut (ι.lang⁻¹ * f.lang) P)) =
      AuxiliaryRel.root (RootPattern.transportAut f.lang P)
    rw [← RootPattern.transportAut_mul]
    simp [← mul_assoc]
  have hMap : B.rel
      ((auxiliaryAction G k).onRel f.lang (AuxiliaryRel.root P))
      (f ∘ xs) :=
    (Structure.Automorphism.map_rel_iff
      f (AuxiliaryRel.root P) xs).2 hR
  have hTuple : (f ∘ xs) = (ι.toFun ∘ ts) := by
    funext j
    exact hPoints j
  have hSource :
      (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.root (RootPattern.transportAut g P)) ts := by
    apply (ι.map_rel_iff
      (AuxiliaryRel.root (RootPattern.transportAut g P)) ts).1
    rw [hLabel, ← hTuple]
    exact hMap
  have hCoord : (ts i).val = g.1 (P.tuple i) :=
    ((auxiliaryRootStructure_root G k n S
      (RootPattern.transportAut g P) ts).mp hSource).2 i
  refine ⟨ts i, ?_, ?_⟩
  · simpa only [hw] using hPoints i
  · simpa only [hr] using hCoord

/-- If the same automorphism moves both supports into A₁, two
realized roots corresponding to the same template root are equal,
even though the supports need not be nested. -/
theorem rootMatches_eq_of_common_move
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p q : CanonicalNonroot G k B)
    (hp : ∀ w ∈ p.support, ∃ t : RootsIn G k S, f w = ι t)
    (hq : ∀ w ∈ q.support, ∃ t : RootsIn G k S, f w = ι t)
    {r : V} {w z : W}
    (hmp : RootMatches G k B p r w)
    (hmq : RootMatches G k B q r z) : w = z := by
  obtain ⟨s, hs, hsr⟩ :=
    rootMatches_alignment_under_move G k S B ι f p hp hmp
  obtain ⟨t, ht, htr⟩ :=
    rootMatches_alignment_under_move G k S B ι f q hq hmq
  have hst : s = t := by
    apply Subtype.ext
    exact hsr.trans htr.symm
  apply f.toEquiv.injective
  calc
    f w = ι s := hs
    _ = ι t := congrArg ι hst
    _ = f z := ht.symm

/-- A fixed common move of two canonical root supports forces them
to be equal when their template centres are equal. -/
theorem canonicalNonroot_support_eq_of_common_move
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p q : CanonicalNonroot G k B)
    (hc : p.center = q.center)
    (hp : ∀ w ∈ p.support, ∃ t : RootsIn G k S, f w = ι t)
    (hq : ∀ w ∈ q.support, ∃ t : RootsIn G k S, f w = ι t) :
    p.support = q.support := by
  have hIncl
      (p q : CanonicalNonroot G k B)
      (hcenter : p.center = q.center)
      (hp : ∀ w ∈ p.support, ∃ t : RootsIn G k S, f w = ι t)
      (hq : ∀ w ∈ q.support, ∃ t : RootsIn G k S, f w = ι t) :
      p.support ⊆ q.support := by
    intro w hw
    obtain ⟨r, hpr⟩ := RootMatches.exists_of_support p hw
    have hrq : r ∈ G.roots k q.center := by
      have hrp := RootMatches.root_mem p hpr
      simpa only [hcenter] using hrp
    obtain ⟨z, hqz⟩ := RootMatches.exists_of_root q hrq
    have hwz : w = z :=
      rootMatches_eq_of_common_move G k S B ι f p q hp hq hpr hqz
    rw [hwz]
    exact RootMatches.support_mem q hqz
  exact Set.Subset.antisymm
    (hIncl p q hc hp hq)
    (hIncl q p hc.symm hq hp)

/-- Under a common source move, equality of projection *already*
implies equality of the canonical reconstructed non-root vertex. -/
theorem canonicalNonroot_eq_of_common_move
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p q : CanonicalNonroot G k B)
    (hc : p.center = q.center)
    (hp : ∀ w ∈ p.support, ∃ t : RootsIn G k S, f w = ι t)
    (hq : ∀ w ∈ q.support, ∃ t : RootsIn G k S, f w = ι t) :
    p = q :=
  CanonicalNonroot.eq_of_center_support p q hc
    (canonicalNonroot_support_eq_of_common_move
      G k S B ι f p q hc hp hq)

end AllThoseEPPA.Applications.KOrientations
