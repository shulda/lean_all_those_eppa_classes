import AllThoseEPPA.Applications.KOrientations.IdentityChartSupport
import AllThoseEPPA.Substructure

/-!
# The canonical original source embeds directly in the reconstructed d-witness

The local d-trace isomorphism for the *identity* auxiliary
automorphism gives a function-exact embedding from the source
d-trace into the full supported piece. Composing with the canonical
closed-substructure inclusion produces a literal embedding into the
complete reconstructed d-witness, which is the natural second-stage
inclusion used in the final EPPA statement.

The induced range is exactly the entire supported piece of
reconstructed vertices whose B₁-root support lies in the image of
the original root-source embedding.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The d-trace of the original source S embeds in the complete
reconstructed d-structure via its canonical source copy. -/
noncomputable def faithful_reconstructed_original_dTraceEmbedding
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι) :
    Structure.Embedding dTrivialAction
      (dTraceStructure G k S)
      (dStructure (faithfulReconstructedDigraph G k S B ι hFaith) k) :=
  (Structure.inclusion dTrivialAction
    (dStructure (faithfulReconstructedDigraph G k S B ι hFaith) k)
    {z | IsMovedSupport G k S B ι (Structure.Automorphism.id B) z}
    (faithful_reconstructed_local_chart_isClosed
      G k S hBound hClosed hRooted B ι hFaith
      (Structure.Automorphism.id B))).comp
    (faithful_reconstructed_local_dTraceEmbedding
      G k S hBound hClosed hRooted B ι hFaith
      (Structure.Automorphism.id B))

/-- The source d-trace embedding has image exactly equal to the
canonical supported piece over the distinguished B₁-root copy. -/
theorem faithful_reconstructed_original_dTraceEmbedding_range
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι) :
    Set.range
      (faithful_reconstructed_original_dTraceEmbedding
        G k S hBound hClosed hRooted B ι hFaith).toFun =
      reconstructedSupportedPiece G k B (Set.range ι.toFun) := by
  have hChart := identity_local_chart_eq_supportedPiece
    G k S B ι
  rw [← hChart]
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change IsMovedSupport G k S B ι (Structure.Automorphism.id B)
      (inverseSourceChart
        G k S hClosed hRooted B ι hFaith
        (Structure.Automorphism.id B) x).val
    exact (inverseSourceChart
      G k S hClosed hRooted B ι hFaith
      (Structure.Automorphism.id B) x).property
  · intro hz
    let q : LocalReconstructedCarrier G k S B ι
        (Structure.Automorphism.id B) := ⟨z, hz⟩
    obtain ⟨x, hEq⟩ :=
      (faithful_reconstructed_local_dTraceEmbedding_bijective
        G k S hBound hClosed hRooted B ι hFaith
        (Structure.Automorphism.id B)).2 q
    refine ⟨x, ?_⟩
    have hval := congrArg Subtype.val hEq
    exact hval

end AllThoseEPPA.Applications.KOrientations
