import AllThoseEPPA.Applications.KOrientations.ReconstructionLocalizeSource
import AllThoseEPPA.Applications.KOrientations.SourceReconstructionSupports
import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportEquivariance

/-!
# Every intrinsic support root is genuinely reachable

This is the missing constructive inclusion in the equation
`roots_B(u) = support(u)`.

Move the entire support of an arbitrary reconstructed vertex u into
the original auxiliary root sort by a *single* B₁ automorphism f.
Local source correspondence identifies f(u) with the canonical
reconstruction of some vertex x in S. The source-copy support theorem
identifies f(support(u)) with the complete root set of x, and the
source-copy path-lifting theorem gives an actual reconstructed path
from f(u) to each image root f(r).

Since the induced B₁ automorphism preserves and reflects directed
paths in the reconstructed graph, applying f⁻¹ gives a path u→r.
No assumptions that the ambient B₀ is rooted, and no circular use of
the final d-class membership theorem, occur anywhere in the proof.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The constructive reverse inclusion: every point of the intrinsic
canonical support of a reconstructed vertex is reachable from it by
a directed path ending in the B₁ root sort. -/
theorem faithful_reconstructed_support_reachable
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S)
    (hRooted : ∀ x : V, x ∈ S → (G.roots k x).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (z : ReconstructedCarrier G k B)
    (r : W)
    (hr : r ∈ reconstructedSupport G k B z) :
    (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
      z (.inl r) := by
  obtain ⟨f, x, hCopy, _⟩ :=
    faithful_reconstructed_vertex_localizes
      G k S hClosed hRooted B ι hFaith z
  have hMoved :
      f r ∈ reconstructedSupport G k B
        (reconstructedVertexPerm G k B f z) := by
    rw [faithful_reconstructedSupport_map
      G k S B ι hFaith f z]
    exact ⟨r, hr, rfl⟩
  have hAtSource :
      f r ∈ reconstructedSupport G k B
        (sourceReconstructedVertex G k S hClosed hRooted B ι x) := by
    rw [← hCopy]
    exact hMoved
  have hLifted :
      (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
        (sourceReconstructedVertex G k S hClosed hRooted B ι x)
        (.inl (f r)) :=
    sourceReconstructedVertex_support_reachable
      G k S hClosed hRooted B ι hFaith x (f r) hAtSource
  have hTransformed :
      (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
        (reconstructedVertexPerm G k B f z)
        (reconstructedVertexPerm G k B f (.inl r)) := by
    change (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
      (reconstructedVertexPerm G k B f z) (.inl (f r))
    rw [hCopy]
    exact hLifted
  exact (faithful_reconstructed_reaches_iff_map
    G k S B ι hFaith f z (.inl r)).mpr hTransformed

end AllThoseEPPA.Applications.KOrientations
