import AllThoseEPPA.Applications.KOrientations.RootedKOrientationDFinalEPPA

/-!
# Public API: coherent faithful EPPA for rooted k-orientations with d-closures

The concrete Section 9.3 / `thm:DF` application of
*All those EPPA classes* is now a verified theorem, not an
axiom or an unchecked reduction.

A finite oriented graph of outdegree at most k is **rooted**
when each vertex reaches a vertex of outdegree strictly below k.
The genuine d-language carries a unary successor operation AND
set-valued F_n operations for ALL positive n. No unary-only
approximation of the original d-language is made.

For every such input, the output is an actual finite rooted
k-orientation and an exact embedding of the ORIGINAL full
d-structure with both coherent EPPA and irreducible-structure
faithfulness.

For downstream projects prefer:

    import AllThoseEPPA.KOrientationsEPPA

The lower-level implementation theorem is
`Applications.KOrientations.exists_rootedKOrientation_faithfulCoherentDEPPa`.
This facade keeps the result discoverable without importing the
umbrella file `AllThoseEPPA` or referring to either internal
EPPA witness selector or the auxiliary language with nontrivial
automorphism-group action.
-/

namespace AllThoseEPPA.KOrientationsEPPA

open Applications.KOrientations

universe u

/-- Rooted finite k-orientations have coherent, irreducible-structure
faithful EPPA in the **entire** higher-arity d-closure language.

This is the direct reusable version of manuscript `thm:DF`
for rooted k-orientations, with the witness required to remain
an actual finite rooted k-orientation. -/
theorem rootedFaithfulCoherent
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
  exists_rootedKOrientation_faithfulCoherentDEPPa
    A k hBound hRooted

/-- The same theorem with only **ordinary** EPPA required.
The proof actually extracts an ordinary extension from the
full coherent witness, keeping the same original d-embedding
and irreducible-structure faithfulness. -/
theorem rootedFaithfulOrdinary
    {V : Type u} [Fintype V]
    (A : Digraph V) (k : ℕ)
    (hBound : A.HasOutdegreeAtMost k)
    (hRooted : A.HasReachableRoots k) :
    ∃ (W : Type u) (_ : Fintype W)
      (K : KOrientation W k)
      (ψ : Structure.Embedding dTrivialAction
        (dStructure A k) (dStructure K.graph k)),
      K.graph.HasReachableRoots k ∧
      Structure.IsEPPAWitness dTrivialAction ψ ∧
      Structure.IsIrreducibleStructureFaithful dTrivialAction ψ := by
  obtain ⟨W, hFinW, K, ψ, hKRooted, ⟨c⟩, hFaith⟩ :=
    rootedFaithfulCoherent A k hBound hRooted
  exact ⟨W, hFinW, K, ψ, hKRooted,
    c.isEPPAWitness dTrivialAction, hFaith⟩

end AllThoseEPPA.KOrientationsEPPA
