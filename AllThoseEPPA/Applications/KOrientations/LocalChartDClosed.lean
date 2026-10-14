import AllThoseEPPA.Applications.KOrientations.ReconstructionRootedDResult
import AllThoseEPPA.Applications.KOrientations.LocalCorrespondenceDClosed

/-!
# Unconditional d-closedness of the local support charts

The previously certified support-moved-domain closure criterion asked
for the exact root/support identity explicitly. The complete source
localization theorem now *proves* that identity under the real
hypotheses: a bounded-degree template and a rooted successor-closed
distinguished source.

Thus every local support chart defined by a B₁ automorphism is closed
under unary successor reachability and all higher root-fibre functions
of the genuinely reconstructed d-structure, with no extra hypothesis
on the second witness being rooted.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every moved-support chart of the reconstructed d-structure is
closed under all of its set-valued functions, in arbitrary arity. -/
theorem faithful_reconstructed_local_chart_isDClosed
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    (faithfulReconstructedDigraph G k S B ι hFaith).IsDClosed
      k {z | IsMovedSupport G k S B ι f z} := by
  have hRoots :=
    (faithful_reconstructed_exact_roots_and_rooted
      G k S hBound hClosed hRooted B ι hFaith).2
  exact isMovedSupport_set_isDClosed_of_exact_roots
    G k S B ι hFaith f hRoots


/-- The same local chart is literally a closed substructure in the
general set-valued-function Structure API used by the EPPA theorem. -/
theorem faithful_reconstructed_local_chart_isClosed
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    (dStructure (faithfulReconstructedDigraph G k S B ι hFaith) k).IsClosed
      {z | IsMovedSupport G k S B ι f z} := by
  exact (dStructure_isClosed_iff
    (faithfulReconstructedDigraph G k S B ι hFaith) k
    {z | IsMovedSupport G k S B ι f z}).mpr
    (faithful_reconstructed_local_chart_isDClosed
      G k S hBound hClosed hRooted B ι hFaith f)

end AllThoseEPPA.Applications.KOrientations
