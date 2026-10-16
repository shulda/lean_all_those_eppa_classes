import AllThoseEPPA.Applications.KOrientations.FirstStageSelectedAuxRootCoherentTriples
import AllThoseEPPA.Applications.KOrientations.SelectedReconstructedDAutomorphism
import AllThoseEPPA.Applications.KOrientations.FullDAutomorphismFunctorial

/-!
# Ordered coherent triples of the ACTUAL second-selected automorphisms

For any coherent triple of partial automorphisms of the ORIGINAL
full d(A)-structure, with its complete arbitrary-arity set-valued
F_n symbols, the first selected successor witness induces an
ACTUAL coherent triple of finite Γ-root partial automorphisms.

The second coherent EPPA selector extends precisely those three
partial automorphisms. The public selector coherence property
therefore proves the ordered identity f_r = f_q.comp f_p
for the actual TOTAL B₁ automorphisms; there are no choices of
posthoc lifts or off-domain extensions in this statement.

The previously certified all-arity reconstructed d-language
automorphism construction preserves ordered composition. Thus the
two genuinely selected EPPA stages together define a coherent
assignment of TOTAL automorphisms on the WHOLE reconstructed
d-structure, not merely on its graph reduct or root sort.

This closes the algebraic coherence obligation, not the geometric
extension-along-the-ORIGINAL-embedding square on nonroot points.
The final coherent EPPA witness theorem is not asserted here.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v w

/-- Coherent triples of actual original full-d partial maps
select an ordered coherent triple of the genuinely chosen
TOTAL auxiliary B₁ automorphisms, including the nonfaithful
Aut(B₀) language action. -/
theorem firstStage_selectedSecondAuxExtension_coherentTriple
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
    (p q r : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (hTriple : Structure.PartialIsomorphism.CoherentTriple p q r) :
    firstStage_selectedSecondAuxExtension A G k ι s B κ t r =
      (firstStage_selectedSecondAuxExtension A G k ι s B κ t q).comp
        (firstStage_selectedSecondAuxExtension A G k ι s B κ t p) := by
  exact t.coherent
    (firstStage_selectedAuxRootPartialAutomorphism A G k ι s p)
    (firstStage_selectedAuxRootPartialAutomorphism A G k ι s q)
    (firstStage_selectedAuxRootPartialAutomorphism A G k ι s r)
    (firstStage_selectedAuxRootPartialAutomorphism_coherentTriple
      A G k ι s p q r hTriple)

/-- The actual selected total automorphisms of the ENTIRE
reconstructed d-language respect ordered coherent triples of
original full-d partial automorphisms. All positive-arity
F_n fibres and both root/nonroot sorts are preserved by the
underlying certified functorial automorphism lift. -/
theorem firstStage_selectedReconstructedDAutomorphism_coherentTriple
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
    (p q r : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (hTriple : Structure.PartialIsomorphism.CoherentTriple p q r) :
    firstStage_selectedReconstructedDAutomorphism
      A G k ι s B κ t hFaith r =
      (firstStage_selectedReconstructedDAutomorphism
        A G k ι s B κ t hFaith q).comp
      (firstStage_selectedReconstructedDAutomorphism
        A G k ι s B κ t hFaith p) := by
  change
    faithful_reconstructed_dAutomorphism_of_auxAutomorphism
      G k (Set.range ι.toFun) B κ hFaith
      (firstStage_selectedSecondAuxExtension A G k ι s B κ t r) =
    (faithful_reconstructed_dAutomorphism_of_auxAutomorphism
      G k (Set.range ι.toFun) B κ hFaith
      (firstStage_selectedSecondAuxExtension A G k ι s B κ t q)).comp
    (faithful_reconstructed_dAutomorphism_of_auxAutomorphism
      G k (Set.range ι.toFun) B κ hFaith
      (firstStage_selectedSecondAuxExtension A G k ι s B κ t p))
  rw [firstStage_selectedSecondAuxExtension_coherentTriple
    A G k ι s B κ t p q r hTriple]
  exact faithful_reconstructed_dAutomorphism_comp
    G k (Set.range ι.toFun) B κ hFaith
    (firstStage_selectedSecondAuxExtension A G k ι s B κ t q)
    (firstStage_selectedSecondAuxExtension A G k ι s B κ t p)

end AllThoseEPPA.Applications.KOrientations
