import AllThoseEPPA.Applications.KOrientations.FirstStageSelectedAuxRootEquivalence
import AllThoseEPPA.Applications.KOrientations.SecondWitness

/-!
# Actual second coherent EPPA selector for original full-d partial maps

Given the first chosen coherent successor EPPA selector on B₀ and
a second coherent auxiliary Γ-root EPPA selector on B₁, a partial
automorphism p of the ORIGINAL all-arity set-valued d(A)
induces the ACTUAL closed Γ-root partial automorphism in B₀.
Apply the second selector to that genuine partial automorphism.

We package the resulting TOTAL auxiliary-language B₁ automorphism
without choosing a graph automorphism or a language-symbol lift
after the fact. It extends the exact selected source partial map
along the second witness embedding.

Crucially this choice respects mathematical Equivalent of original
d-partial maps: first selected Γ-root inputs are Equivalent on
their actual closed source, and the second coherent extension
identifies their total B₁ extensions. All R_P/E_P relation
symbols and unary fibre conditions remain those of the original
second auxiliary action, with possible NONFAITHFUL Γ-label action.

The coherence-of-triples property needs the separately verified
actual first-to-second Γ-root triple lemma; final reconstructed
d-extension and EPPA gluing are still independent obligations.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v w

/-- Total second-stage auxiliary witness automorphism SELECTED
from an original full d(A)-partial automorphism, via the
actual first-stage coherent graph selector and its induced
exact closed-domain Γ-root partial automorphism. -/
noncomputable def firstStage_selectedSecondAuxExtension
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
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k)) :
    Structure.Automorphism (auxiliaryAction G k) B :=
  t.extension (firstStage_selectedAuxRootPartialAutomorphism A G k ι s p)

/-- The actual chosen TOTAL B₁ automorphism extends the
genuine selected Γ-root source partial automorphism, including
the language group component in the correct action order. -/
theorem firstStage_selectedSecondAuxExtension_extendsRoot
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
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k)) :
    Structure.ExtendsAlong (auxiliaryAction G k) κ
      (firstStage_selectedAuxRootPartialAutomorphism A G k ι s p)
      (firstStage_selectedSecondAuxExtension A G k ι s B κ t p) :=
  t.extension_spec _

/-- The ACTUAL SECOND chosen total B₁ automorphism is independent
of equivalent presentations of any original d(A)-partial map.
No equality of off-domain PartialEquiv fallback values is assumed. -/
theorem firstStage_selectedSecondAuxExtension_respectsEquivalent
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
    (p q : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    firstStage_selectedSecondAuxExtension A G k ι s B κ t p =
      firstStage_selectedSecondAuxExtension A G k ι s B κ t q :=
  t.respects_equivalent _ _
    (firstStage_selectedAuxRootPartialAutomorphism_respectsEquivalent
      A G k ι s p q hpq)

end AllThoseEPPA.Applications.KOrientations
