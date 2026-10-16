import AllThoseEPPA.Applications.KOrientations.SelectedSecondAuxCoherentExtension
import AllThoseEPPA.Applications.KOrientations.FullDAutomorphismFunctorial

/-!
# Actual selected TOTAL reconstructed d-automorphism for an original d-partial map

The first coherent successor EPPA selector assigns a real whole
B₀ graph automorphism to every original full all-arity d(A)
partial automorphism. Its exact Γ-root restriction is a valid
closed partial automorphism of the second auxiliary source.
The second coherent Γ-root selector assigns a true TOTAL B₁
automorphism. Independently, the choice-free reconstruction
already lifts EVERY B₁ automorphism to a true total automorphism
of ALL relations and set-valued functions of the reconstructed
full d-language.

Compose these certified constructions. The output is NOT merely
a graph permutation or a unary successor action: it is the
actual public Structure.Automorphism dTrivialAction of the entire
reconstructed d-structure. It comes with a definitional vertex
formula and respects Equivalent original d-partial maps.

Its full extension-along-original-d(A) equation, coherent
composition and irreducible faithfulness of the final embedding
remain distinct proof obligations.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v w

/-- Selected TOTAL reconstructed-d automorphism arising from the
genuine FIRST and SECOND coherent selector choices for any
original full all-arity d(A)-partial automorphism. -/
noncomputable def firstStage_selectedReconstructedDAutomorphism
    {V : Type u} {W : Type v} {X : Type w}
    [Fintype V] [Fintype W] [Fintype X]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (B : Structure (auxiliaryLanguage G k) X)
    (κ : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k (Set.range ι.toFun)) B)
    (t : Structure.CoherentExtension (auxiliaryAction G k) κ)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) κ)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k)) :
    Structure.Automorphism dTrivialAction
      (dStructure (faithfulReconstructedDigraph G k
        (Set.range ι.toFun) B κ hFaith) k) :=
  faithful_reconstructed_dAutomorphism_of_auxAutomorphism
    G k (Set.range ι.toFun) B κ hFaith
    (firstStage_selectedSecondAuxExtension A G k ι s B κ t p)

/-- The selected full-d automorphism has precisely the
canonical reconstructed root/nonroot permutation induced by
the actual SECOND chosen B₁ automorphism. -/
theorem firstStage_selectedReconstructedDAutomorphism_apply
    {V : Type u} {W : Type v} {X : Type w}
    [Fintype V] [Fintype W] [Fintype X]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (B : Structure (auxiliaryLanguage G k) X)
    (κ : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k (Set.range ι.toFun)) B)
    (t : Structure.CoherentExtension (auxiliaryAction G k) κ)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) κ)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (z : ReconstructedCarrier G k B) :
    firstStage_selectedReconstructedDAutomorphism
      A G k ι s B κ t hFaith p z =
    reconstructedVertexPerm G k B
      (firstStage_selectedSecondAuxExtension A G k ι s B κ t p) z :=
  faithful_reconstructed_dAutomorphism_apply
    G k (Set.range ι.toFun) B κ hFaith
    (firstStage_selectedSecondAuxExtension A G k ι s B κ t p) z

/-- Equivalence of original full-d partial maps selects the
SAME total reconstructed d-automorphism: both coherent
selection steps respect Equivalent and the reconstruction
uses no subsequent arbitrary permutation choice. -/
theorem firstStage_selectedReconstructedDAutomorphism_respectsEquivalent
    {V : Type u} {W : Type v} {X : Type w}
    [Fintype V] [Fintype W] [Fintype X]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (B : Structure (auxiliaryLanguage G k) X)
    (κ : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k (Set.range ι.toFun)) B)
    (t : Structure.CoherentExtension (auxiliaryAction G k) κ)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) κ)
    (p q : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    firstStage_selectedReconstructedDAutomorphism
      A G k ι s B κ t hFaith p =
    firstStage_selectedReconstructedDAutomorphism
      A G k ι s B κ t hFaith q :=
  congrArg
    (faithful_reconstructed_dAutomorphism_of_auxAutomorphism
      G k (Set.range ι.toFun) B κ hFaith)
    (firstStage_selectedSecondAuxExtension_respectsEquivalent
      A G k ι s B κ t p q hpq)

end AllThoseEPPA.Applications.KOrientations
