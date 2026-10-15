import AllThoseEPPA.Applications.KOrientations.FirstStageDTraceBridge
import AllThoseEPPA.Applications.KOrientations.OriginalSourceDTraceEmbedding

/-!
# Canonical embedding of the actual original d-structure into reconstruction

Suppose A is a rooted k-orientation, G is its first-stage exact
successor-language faithful EPPA witness, and B₁ is the second-stage
faithful auxiliary EPPA witness over the embedded source S=ι₀(A).

Two already-checked local interfaces compose:

  d(A) -- exact first-stage d-trace bridge --> dTrace_G(S)
       -- identity-chart embedding --> d(Reconstruction(G,B₁)).

This is a real `Structure.Embedding` in the full d-language, with
all F_n interpreted as set-valued functions. It requires only
successor-closedness of S, inherited from the first embedding, and
reachable roots in the original A. It does *not* assume the first
witness G is rooted or that S is ambient d-closed.

This constructs the input embedding needed by EPPA. Showing all
partial automorphisms extend coherently remains a separate task.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v w

/-- Two-stage reconstructed d-structure contains an exact copy of
the original rooted input, with no ambient d-closure assumption. -/
noncomputable def faithful_reconstructed_original_input_dEmbedding
    {U : Type u} {V : Type v} {W : Type w}
    [Fintype U] [Fintype V] [Fintype W]
    (A : Digraph U) (G : Digraph V) (k : ℕ)
    (hBound : G.HasOutdegreeAtMost k)
    (hRootedA : A.HasReachableRoots k)
    (ι₀ : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (B₁ : Structure (auxiliaryLanguage G k) W)
    (ι₁ : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k (Set.range ι₀.toFun)) B₁)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι₁) :
    Structure.Embedding dTrivialAction
      (dStructure A k)
      (dStructure
        (faithfulReconstructedDigraph G k
          (Set.range ι₀.toFun) B₁ ι₁ hFaith) k) :=
  (faithful_reconstructed_original_dTraceEmbedding
      G k (Set.range ι₀.toFun) hBound
      (successorEmbedding_image_successorClosed A G ι₀)
      (successorEmbedding_image_rooted A G k hRootedA ι₀)
      B₁ ι₁ hFaith).comp
    (successorEmbedding_to_dTrace A G k ι₀)

end AllThoseEPPA.Applications.KOrientations
