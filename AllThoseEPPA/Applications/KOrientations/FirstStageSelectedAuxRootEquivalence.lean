import AllThoseEPPA.Applications.KOrientations.FirstStageSelectedAuxRootPartialAutomorphism
import AllThoseEPPA.Applications.KOrientations.FirstStageSelectedGraphCoherence
import AllThoseEPPA.Applications.KOrientations.AuxiliaryClosedRootEquivalentData

/-!
# Equivalence naturality of the ACTUAL first-to-second k-orientation selector input

The real original full arbitrarily high-arity d(A) partial map p
is first sent to the true selected B₀ successor automorphism and
its group element g_p∈Aut(B₀), then to a genuine full Γ-language
root partial automorphism on the closed d-trace image E[p.source].

Two ORIGINAL mathematical partial automorphisms are equivalent
when they have the same source and agree on that source (not
when their arbitrary outside-domain total functions are equal).
This condition also implies equality of their target sets.
The FIRST coherent EPPA selector independently ensures that
their ACTUAL chosen B₀ graph automorphisms g_p and g_q agree.

The auxiliary root Γ-partial isomorphism depends only on
these exact source and range sets and the group element, not
on any proof witnesses of closure or image equality. Thus
equivalent original d-partial maps give Equivalent ACTUAL
second-selector source partial automorphisms, preserving
the full possibly nonfaithful Γ-action on all R_P/E_P labels,
the exact unary function fibres and all F_n source closures.
No global selected g[S]=S or ambient S d-closedness assumed.

The coherent triple and gluing of the two selected extensions
are separate follow-up obligations.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Mathematical Equivalent of two original entire d-language
partial automorphisms is preserved by the ACTUAL chosen first
EPPA selector followed by the induced second auxiliary Γ-root
partial automorphism. No false equality of outside-source
PartialEquiv default values is needed. -/
theorem firstStage_selectedAuxRootPartialAutomorphism_respectsEquivalent
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (p q : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    Structure.PartialIsomorphism.Equivalent
      (firstStage_selectedAuxRootPartialAutomorphism A G k ι s p)
      (firstStage_selectedAuxRootPartialAutomorphism A G k ι s q) := by
  let E := firstStageFullDSourceEmbedding A G k ι
  have hs : E.toFun '' p.source = E.toFun '' q.source :=
    congrArg (fun T : Set V => E.toFun '' T)
      (PartialEquiv.EqOnSource.source_eq hpq.2)
  have ht : E.toFun '' p.target = E.toFun '' q.target :=
    congrArg (fun T : Set V => E.toFun '' T)
      (PartialEquiv.EqOnSource.target_eq hpq.2)
  have hg :
      graphAutOfSuccessorAut G
        (s.extension (dPartialAutomorphism_to_successor A k p)) =
      graphAutOfSuccessorAut G
        (s.extension (dPartialAutomorphism_to_successor A k q)) :=
    firstStage_coherentSelector_graphAut_respectsEquivalent
      A G k ι s p q hpq
  exact auxiliaryClosedRootPartialIsomorphism_equivalent_of_equal_data
    G k (Set.range ι.toFun)
    (E.toFun '' p.source) (E.toFun '' p.target)
    (E.toFun '' q.source) (E.toFun '' q.target)
    (firstStage_dPartialSourceTrace_isClosed A G k ι p)
    (firstStage_dPartialTargetTrace_isClosed A G k ι p)
    (firstStage_dPartialSourceTrace_isClosed A G k ι q)
    (firstStage_dPartialTargetTrace_isClosed A G k ι q)
    (graphAutOfSuccessorAut G
      (s.extension (dPartialAutomorphism_to_successor A k p)))
    (graphAutOfSuccessorAut G
      (s.extension (dPartialAutomorphism_to_successor A k q)))
    (firstStage_selectedGraphAut_dTraceDomainImage A G k ι s p)
    (firstStage_selectedGraphAut_dTraceDomainImage A G k ι s q)
    hs ht hg

end AllThoseEPPA.Applications.KOrientations
