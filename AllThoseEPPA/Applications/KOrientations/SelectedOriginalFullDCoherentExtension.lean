import AllThoseEPPA.Applications.KOrientations.SelectedOriginalFullDExtendsAlong
import AllThoseEPPA.Applications.KOrientations.SelectedReconstructedCoherence
import AllThoseEPPA.Applications.KOrientations.OriginalDFaithfulReconstruction

/-!
# Coherent and irreducible-faithful EPPA for the ACTUAL original d(A)

This is the internal two-stage k-orientation application theorem
for any concrete pair of genuine coherent EPPA selectors.
First, the actual first witness embeds the entire original
positive-arity set-valued d-language into its successor encoding.
Second, its honest intrinsic source trace is embedded by the
canonical supported-piece map into the full reconstructed witness.

The selected TOTAL reconstructed full-d automorphisms now have
all three EXACT PUBLIC coherent-extension properties:
* ExtendsAlong on the actual full original d(A) embedding,
  including all original roots and nonroots,
* respect equivalent original d-partial isomorphisms,
* preserve ordered coherent triples.

The original full embedding is independently genuinely
irreducible-structure faithful. No post hoc choice of automorphisms,
ambient original-source d-closedness, wrong trivialization of the
second auxiliary group component, or fake unary-only F_n reduction.
Finite witness existence and recognition as a k-orientation still
require their actual selector-existence and reconstruction closure APIs.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v w

/-- Both REAL selected EPPA extensions together give a
coherent extension family of the ORIGINAL full all-arity
d(A), along its genuine faithful reconstructed d-embedding.
This is not only an abstract translated successor/Γ-source
extension: the ExtendsAlong square is certified at every old
d(A) vertex and for all original partial automorphisms. -/
noncomputable def firstStage_originalDReconstructedCoherentExtension
    {V : Type u} {W : Type v} {X : Type w}
    [Fintype V] [Fintype W] [Fintype X]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (hBound : G.HasOutdegreeAtMost k)
    (hRooted : A.HasReachableRoots k)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (B : Structure (auxiliaryLanguage G k) X)
    (κ : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k (Set.range ι.toFun)) B)
    (t : Structure.CoherentExtension (auxiliaryAction G k) κ)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) κ) :
    Structure.CoherentExtension dTrivialAction
      (firstStage_originalDReconstructedEmbedding
        A G k hBound hRooted ι B κ hFaith) where
  extension := firstStage_selectedReconstructedDAutomorphism
    A G k ι s B κ t hFaith
  extension_spec := by
    intro p
    exact firstStage_selectedReconstructedDAutomorphism_original_extendsAlong
      A G k hBound hRooted ι s B κ t hFaith p
  respects_equivalent := by
    intro p q hpq
    exact firstStage_selectedReconstructedDAutomorphism_respectsEquivalent
      A G k ι s B κ t hFaith p q hpq
  coherent := by
    intro p q r hTriple
    exact firstStage_selectedReconstructedDAutomorphism_coherentTriple
      A G k ι s B κ t hFaith p q r hTriple

/-- The ORIGINAL (not just supported-chart) reconstructed
witness is coherently EPPA and irreducible-structure faithful
for its honest entire positive-arity d(A)-language embedding,
conditional only on the actual input pair of coherent selectors. -/
theorem firstStage_originalDReconstructed_coherentFaithful
    {V : Type u} {W : Type v} {X : Type w}
    [Fintype V] [Fintype W] [Fintype X]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (hBound : G.HasOutdegreeAtMost k)
    (hRooted : A.HasReachableRoots k)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (B : Structure (auxiliaryLanguage G k) X)
    (κ : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k (Set.range ι.toFun)) B)
    (t : Structure.CoherentExtension (auxiliaryAction G k) κ)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) κ) :
    Structure.IsCoherentEPPAWitness dTrivialAction
      (firstStage_originalDReconstructedEmbedding
        A G k hBound hRooted ι B κ hFaith) ∧
    Structure.IsIrreducibleStructureFaithful dTrivialAction
      (firstStage_originalDReconstructedEmbedding
        A G k hBound hRooted ι B κ hFaith) := by
  refine ⟨⟨firstStage_originalDReconstructedCoherentExtension
    A G k hBound hRooted ι s B κ t hFaith⟩, ?_⟩
  exact firstStage_originalDReconstructedEmbedding_irreducibleFaithful
    A G k hBound hRooted ι B κ hFaith

end AllThoseEPPA.Applications.KOrientations
