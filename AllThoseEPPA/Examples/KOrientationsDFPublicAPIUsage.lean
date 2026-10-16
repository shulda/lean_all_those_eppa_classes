import AllThoseEPPA.KOrientationsEPPA

/-!
# Downstream import-only regression for the rooted k-orientation d-EPPA API

This file intentionally imports ONLY the supported public facade.
It compiles in the entire library CI and audit, confirming that
another Lean project can invoke the actual finite coherent
faithful witness theorem and extract ordinary EPPA without
accessing internal first- and second-stage construction APIs.

The function symbols F_n of dStructure are genuinely indexed
by every positive arity, not silently restricted to unary symbols.
-/

namespace AllThoseEPPA.KOrientationsEPPA.APIUsage

open Applications.KOrientations

universe u

/-- An external consumer can request the full Section 9.3
coherent and irreducible-structure faithful witness by name. -/
theorem finiteFullDCoherentWitness
    {V : Type u} [Fintype V]
    (A : Digraph V) (k : ℕ)
    (hBound : A.HasOutdegreeAtMost k)
    (hRooted : A.HasReachableRoots k) :
    ∃ (W : Type u) (_ : Fintype W)
      (K : KOrientation W k)
      (ψ : Structure.Embedding dTrivialAction
        (dStructure A k) (dStructure K.graph k)),
      K.graph.HasReachableRoots k ∧
      Structure.IsCoherentEPPAWitness dTrivialAction ψ ∧
      Structure.IsIrreducibleStructureFaithful dTrivialAction ψ :=
  rootedFaithfulCoherent A k hBound hRooted

/-- An external consumer can extract the finite ordinary witness
and its actual rootedness, without ever opening the auxiliary
coherent selector or assuming extra d-closure properties. -/
theorem finiteFullDOrdinaryWitness
    {V : Type u} [Fintype V]
    (A : Digraph V) (k : ℕ)
    (hBound : A.HasOutdegreeAtMost k)
    (hRooted : A.HasReachableRoots k) :
    ∃ (W : Type u) (_ : Fintype W)
      (K : KOrientation W k)
      (ψ : Structure.Embedding dTrivialAction
        (dStructure A k) (dStructure K.graph k)),
      Structure.IsEPPAWitness dTrivialAction ψ ∧
      K.graph.HasReachableRoots k ∧
      Structure.IsIrreducibleStructureFaithful dTrivialAction ψ := by
  obtain ⟨W, hW, K, ψ, hRootedK, hEPPA, hFaith⟩ :=
    rootedFaithfulOrdinary A k hBound hRooted
  exact ⟨W, hW, K, ψ, hEPPA, hRootedK, hFaith⟩

end AllThoseEPPA.KOrientationsEPPA.APIUsage
