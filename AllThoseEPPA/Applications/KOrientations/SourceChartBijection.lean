import AllThoseEPPA.Applications.KOrientations.SourceChartDomain
import AllThoseEPPA.Applications.KOrientations.ReconstructionLocalizeSource

/-!
# Inverse source charts are bijections onto support-moved domains

Fix one B₁ automorphism f. Transport each vertex of the rooted,
successor-closed template source S into the reconstructed graph
and then back by f⁻¹. The support equality proves that its entire
support is moved by f into the canonical source-root sort.

Conversely, the localization theorem for *the same f* shows that
every vertex of this local support chart is obtained that way.
No arbitrary quotient transversal is used. This constructs the
underlying carrier bijection needed for the local closed-piece
isomorphism; its graph and function reflection are separate.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Reconstructed permutations correctly invert the action of
a second-stage automorphism on both disjoint carrier sorts. -/
theorem reconstructedVertexPerm_symm_map
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (z : ReconstructedCarrier G k B) :
    reconstructedVertexPerm G k B f.symm
      (reconstructedVertexPerm G k B f z) = z := by
  cases z with
  | inl w =>
      change Sum.inl (f.symm (f w)) = Sum.inl w
      rw [Structure.Automorphism.symm_apply_apply]
  | inr p =>
      change Sum.inr
        (CanonicalNonroot.map f.symm (CanonicalNonroot.map f p)) =
          Sum.inr p
      rw [CanonicalNonroot.map_symm_apply]

/-- Canonical reverse local chart: source vertices become reconstructed
vertices whose full supports are moved into the root source by f. -/
noncomputable def inverseSourceChart
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    {a : V // a ∈ S} → LocalReconstructedCarrier G k S B ι f :=
  fun x =>
    ⟨reconstructedVertexPerm G k B f.symm
      (sourceReconstructedVertex G k S hClosed hRooted B ι x),
     inverseSourceCopy_isMovedSupport
       G k S hClosed hRooted B ι hFaith f x⟩

/-- The reverse chart is a genuine bijection: its injectivity follows
from the source-copy injection, and surjectivity from the root and
nonroot localization lemmas under this same automorphism f. -/
theorem inverseSourceChart_bijective
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    Function.Bijective
      (inverseSourceChart G k S hClosed hRooted B ι hFaith f) := by
  classical
  constructor
  · intro x y hxy
    have hRaw := congrArg Subtype.val hxy
    change
      reconstructedVertexPerm G k B f.symm
        (sourceReconstructedVertex G k S hClosed hRooted B ι x) =
      reconstructedVertexPerm G k B f.symm
        (sourceReconstructedVertex G k S hClosed hRooted B ι y)
        at hRaw
    exact (sourceReconstructedVertex_injective
      G k S hClosed hRooted B ι)
      ((reconstructedVertexPerm G k B f.symm).injective hRaw)
  · intro t
    obtain ⟨z, hz⟩ := t
    have hCopy :
        ∃ x : {a : V // a ∈ S},
          reconstructedVertexPerm G k B f z =
            sourceReconstructedVertex G k S hClosed hRooted B ι x := by
      cases z with
      | inl a =>
          exact faithful_localize_reconstructed_root
            G k S hClosed hRooted B ι f a
            (hz a (B.mem_closureAtSet a))
      | inr p =>
          exact faithful_localize_reconstructed_nonroot
            G k S hClosed hRooted B ι f p hz
    obtain ⟨x, hEq⟩ := hCopy
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change reconstructedVertexPerm G k B f.symm
      (sourceReconstructedVertex G k S hClosed hRooted B ι x) = z
    rw [← hEq]
    exact reconstructedVertexPerm_symm_map G k B f z

end AllThoseEPPA.Applications.KOrientations
