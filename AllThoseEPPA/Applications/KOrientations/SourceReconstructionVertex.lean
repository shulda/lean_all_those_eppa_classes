import AllThoseEPPA.Applications.KOrientations.SourceReconstructionEdges

/-!
# One intrinsic source-copy map into the reconstructed graph

For each vertex x of the successor-closed rooted source S, define
its image in the reconstructed graph. Root x is mapped through the
actual second-stage root embedding ι₁. Nonroot x is represented by
one complete realized R_P pattern and mapped to its choice-free
canonical pair.

The formula for the new template centre is ι₁.lang(x). This
correctly handles a nonidentity second-stage language component.

All four edge cases have already been proved for arbitrary source
R_P realizations, so the resulting map preserves every directed
edge of the original template restricted to S.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Pick one source R_P realization for a nonroot. Any other choice
gives the same canonical pair by the exact support formula. -/
noncomputable def chosenSourceNonroot
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (x : V) (hx : x ∈ S)
    (hNonroot : ¬ G.IsRoot k x) :
    SourceNonrootPattern G k S x :=
  Classical.choice
    (SourceNonrootPattern.exists_of_nonroot
      (G := G) (k := k) (S := S) (x := x)
      hClosed hRooted hx hNonroot)

/-- The actual source-to-reconstruction vertex map. The image
of a nonroot uses the transported label, so its centre is
ι₁.lang(x), not necessarily x. -/
noncomputable def sourceReconstructedVertex
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (x : {a : V // a ∈ S}) :
    ReconstructedCarrier G k B := by
  classical
  exact if hRoot : G.IsRoot k x.val then
    .inl (ι ⟨x.val, x.property, hRoot⟩)
  else
    .inr ((chosenSourceNonroot G k S hClosed hRooted
      x.val x.property hRoot).toCanonical B ι)

/-- The source-copy vertex map preserves all four edge cases,
using the same arbitrary but fixed source realization choices. -/
theorem sourceReconstructedVertex_preserves_edge
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (x y : {a : V // a ∈ S})
    (hEdge : G.edge x.val y.val) :
    ReconstructedEdge G k B
      (sourceReconstructedVertex G k S hClosed hRooted B ι x)
      (sourceReconstructedVertex G k S hClosed hRooted B ι y) := by
  classical
  by_cases hx : G.IsRoot k x.val
  · by_cases hy : G.IsRoot k y.val
    · simpa only [sourceReconstructedVertex, dif_pos hx, dif_pos hy]
        using source_root_root_edge G k S B ι
          (⟨x.val, x.property, hx⟩ : RootsIn G k S)
          (⟨y.val, y.property, hy⟩ : RootsIn G k S) hEdge
    · simpa only [sourceReconstructedVertex, dif_pos hx, dif_neg hy]
        using source_root_nonroot_edge G k S B ι
          (chosenSourceNonroot G k S hClosed hRooted
            y.val y.property hy)
          (⟨x.val, x.property, hx⟩ : RootsIn G k S) hEdge
  · by_cases hy : G.IsRoot k y.val
    · simpa only [sourceReconstructedVertex, dif_neg hx, dif_pos hy]
        using source_nonroot_root_edge G k S B ι
          (chosenSourceNonroot G k S hClosed hRooted
            x.val x.property hx)
          (⟨y.val, y.property, hy⟩ : RootsIn G k S) hEdge
    · simpa only [sourceReconstructedVertex, dif_neg hx, dif_neg hy]
        using source_nonroot_nonroot_edge G k S B ι
          (chosenSourceNonroot G k S hClosed hRooted
            x.val x.property hx)
          (chosenSourceNonroot G k S hClosed hRooted
            y.val y.property hy) hEdge

/-- Different vertices of S have different reconstructed images.
Root/nonroot tags are disjoint, the root embedding is injective,
and nonroot centres are transported by a genuine permutation. -/
theorem sourceReconstructedVertex_injective
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B) :
    Function.Injective
      (sourceReconstructedVertex G k S hClosed hRooted B ι) := by
  classical
  intro x y hxy
  by_cases hx : G.IsRoot k x.val
  · by_cases hy : G.IsRoot k y.val
    · simp only [sourceReconstructedVertex, dif_pos hx, dif_pos hy]
        at hxy
      have hpre :
          (⟨x.val, x.property, hx⟩ : RootsIn G k S) =
          (⟨y.val, y.property, hy⟩ : RootsIn G k S) :=
        ι.injective (Sum.inl.inj hxy)
      have hval : x.val = y.val :=
        congrArg Subtype.val hpre
      exact Subtype.ext hval
    · simp only [sourceReconstructedVertex, dif_pos hx, dif_neg hy]
        at hxy
      cases hxy
  · by_cases hy : G.IsRoot k y.val
    · simp only [sourceReconstructedVertex, dif_neg hx, dif_pos hy]
        at hxy
      cases hxy
    · simp only [sourceReconstructedVertex, dif_neg hx, dif_neg hy]
        at hxy
      have hc := congrArg CanonicalNonroot.center (Sum.inr.inj hxy)
      have hcentres : ι.lang.1 x.val = ι.lang.1 y.val := by
        simpa only [SourceNonrootPattern.toCanonical_center] using hc
      apply Subtype.ext
      exact ι.lang.1.injective hcentres

end AllThoseEPPA.Applications.KOrientations
