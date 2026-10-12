import AllThoseEPPA.Applications.KOrientations.AuxiliaryLanguage
import AllThoseEPPA.MainTheorems

/-!
# First use of the checked general EPPA theorem

This is an actual invocation of the public main theorem, not a
reimplementation of the valuation construction.

The full application still needs an essential subsequent bridge:
its unrestricted faithful coherent witness must be shown to be
isomorphic to the successor expansion of a finite \(k\)-orientation.
That class-membership transfer is NOT hidden in this statement and
is not claimed proved by this file.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- The trivial language action has finite relabelling orbit
independently of the cardinality of the vertex set. -/
theorem successorStructure_finiteRelabelOrbit {V : Type u}
    (G : Digraph V) :
    (successorStructure G).HasFiniteRelabelOrbit successorAction := by
  unfold Structure.HasFiniteRelabelOrbit
  exact Set.finite_range
    (fun g : PUnit =>
      (successorStructure G).relabel successorAction g)

/-- The first-stage *unrestricted* witness for the successor-closure
encoding. It is already coherent and irreducible-structure faithful;
the later class-membership argument must use that faithfulness to
verify the k-orientation/reachability axioms of its carrier.

This exact result uses \`MainTheorems.unrestrictedFaithfulCoherentEPPA\`.
-/
theorem exists_firstStageUnrestrictedWitness
    {V : Type u} [Finite V] (G : Digraph V) :
    ∃ (W : Type u) (_ : Finite W)
      (B : Structure successorLanguage W)
      (ι : Structure.Embedding successorAction (successorStructure G) B),
      Structure.IsCoherentEPPAWitness successorAction ι ∧
      Structure.IsIrreducibleStructureFaithful successorAction ι := by
  exact MainTheorems.unrestrictedFaithfulCoherentEPPA
    successorAction (successorStructure G)
    (successorStructure_finiteRelabelOrbit G)

end AllThoseEPPA.Applications.KOrientations
