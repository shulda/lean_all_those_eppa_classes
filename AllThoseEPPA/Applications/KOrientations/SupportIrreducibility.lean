import AllThoseEPPA.Applications.KOrientations.SupportedClosedPieces
import AllThoseEPPA.Irreducible

/-!
# Each intrinsic support is an irreducible B₁-substructure

This is the key local irreducibility observation in the proof that
an irreducible reconstructed d-substructure has an irreducible
auxiliary root trace.

A root support is an actual singleton closure in B₁ and hence
irreducible by the general closure-at-point theorem. A canonical
nonroot support is the closure of a realized R_P root tuple:
irreducible-structure faithfulness makes the tuple's range closed,
and the general relation-tuple closure lemma makes its induced
substructure irreducible.

This statement concerns genuine irreducibility under the public
FreeDecomposition definition, not merely graph connectedness.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every reconstructed point carries an irreducible substructure
on its full intrinsic B₁-root support. -/
theorem faithful_reconstructedSupport_auxiliary_isIrreducible
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (z : ReconstructedCarrier G k B) :
    (B.induce (reconstructedSupport G k B z)
      (faithful_reconstructedSupport_auxiliary_isClosed
        G k S B ι hFaith z)).IsIrreducible := by
  cases z with
  | inl a =>
      change (B.closureAt a).IsIrreducible
      exact B.closureAt_isIrreducible a
  | inr p =>
      obtain ⟨n, P, xs, _, hRel, hRange⟩ := p.witnessed
      have hClosed : B.IsClosed (Set.range xs) :=
        faithful_auxiliary_rootTuple_isClosed
          G k S B ι hFaith P xs hRel
      have hEq : B.closureSet (Set.range xs) =
          Set.range xs := B.closureSet_eq_self hClosed
      have hIrred :
          (B.induce (Set.range xs) hClosed).IsIrreducible := by
        simpa only [Structure.closureStructure, hEq] using
          (B.relationTupleClosure_isIrreducible
            (AuxiliaryRel.root P) xs hRel)
      change (B.induce p.support
        (canonicalNonroot_support_isClosed G k S B ι hFaith p)).IsIrreducible
      simpa only [hRange] using hIrred

end AllThoseEPPA.Applications.KOrientations
