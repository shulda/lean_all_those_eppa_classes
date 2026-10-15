import AllThoseEPPA.Applications.KOrientations.LocalChartDTraceIso
import AllThoseEPPA.Applications.KOrientations.SupportedClosedPieces

/-!
# The identity local chart is precisely the canonical source-supported piece

For the identity B₁ automorphism, the predicate `IsMovedSupport`
reduces to containment of the intrinsic reconstructed support in
the actual range of the auxiliary root embedding.

This identifies the canonical local chart on which the source
d-trace is isomorphic with the *fixed source-supported piece*
used in irreducible-structure faithfulness.

The statement is independent of whether the auxiliary B₁ carrier
itself is rooted and does not assume that S is d-closed in B₀.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Identity movement is exactly membership in the canonical
root-supported source piece. -/
theorem identity_isMovedSupport_iff_supported
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (z : ReconstructedCarrier G k B) :
    IsMovedSupport G k S B ι
      (Structure.Automorphism.id B) z ↔
    z ∈ reconstructedSupportedPiece G k B (Set.range ι.toFun) := by
  change
    (∀ w ∈ reconstructedSupport G k B z,
      ∃ t : RootsIn G k S, w = ι t) ↔
    reconstructedSupport G k B z ⊆ Set.range ι.toFun
  constructor
  · intro h w hw
    obtain ⟨t, ht⟩ := h w hw
    exact ⟨t, ht.symm⟩
  · intro h w hw
    obtain ⟨t, ht⟩ := h hw
    exact ⟨t, ht.symm⟩

/-- Equality of the two source-piece carrier sets, not merely a
bijection or one-sided inclusion. -/
theorem identity_local_chart_eq_supportedPiece
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B) :
    {z : ReconstructedCarrier G k B |
      IsMovedSupport G k S B ι (Structure.Automorphism.id B) z} =
      reconstructedSupportedPiece G k B (Set.range ι.toFun) := by
  ext z
  exact identity_isMovedSupport_iff_supported G k S B ι z

end AllThoseEPPA.Applications.KOrientations
