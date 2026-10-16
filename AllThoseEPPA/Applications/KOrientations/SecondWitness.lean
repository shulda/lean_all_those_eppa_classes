import AllThoseEPPA.Applications.KOrientations.AuxiliaryAction
import AllThoseEPPA.MainTheorems

/-!
# Second unrestricted coherent EPPA witness for the root sort

The auxiliary structure lives on the roots of the distinguished
template substructure `S`.  Its relation labels index the entire
ambient finite graph, so the acting group is the actual automorphism
group of that ambient graph (not necessarily a faithful symbol action).

The checked general theorem has only unary-function and finite-orbit
hypotheses, both verified in the preceding modules.  The output is a
raw auxiliary-language EPPA witness B₁; the much harder choice-free
reconstruction of the target d-structure is a separate task.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- **Second invocation** of the checked general unrestricted,
irreducible-structure faithful *coherent* EPPA theorem.

Given any finite template digraph G and distinguished vertex set S,
construct a finite witness for its induced root-only auxiliary
structure, with language action by the full group of graph
automorphisms of G.  No assertion about the reconstructed d-structure
is hidden here. -/
theorem exists_secondStageUnrestrictedWitness
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V) :
    ∃ (W : Type u) (_ : Finite W)
      (B₁ : Structure (auxiliaryLanguage G k) W)
      (ι : Structure.Embedding (auxiliaryAction G k)
        (auxiliaryRootStructure G k S) B₁),
      Structure.IsCoherentEPPAWitness (auxiliaryAction G k) ι ∧
      Structure.IsIrreducibleStructureFaithful (auxiliaryAction G k) ι := by
  exact MainTheorems.unrestrictedFaithfulCoherentEPPA
    (auxiliaryAction G k)
    (auxiliaryRootStructure G k S)
    (auxiliary_finiteRelabelOrbit G k
      (auxiliaryRootStructure G k S))

end AllThoseEPPA.Applications.KOrientations
