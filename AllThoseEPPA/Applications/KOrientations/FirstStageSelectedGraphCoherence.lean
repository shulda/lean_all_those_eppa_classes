import AllThoseEPPA.Applications.KOrientations.FirstStageSelectedGraphDomainImage
import AllThoseEPPA.Applications.KOrientations.DToSuccessorCoherentReduction

/-!
# Actual first-stage B₀ graph automorphisms respect d-map equivalence and coherence

The first coherent EPPA selector is invoked on the UNARY successor
reduct of the genuine original all-arity d-expansion, via the checked
forgetful partial-map construction. The resulting total automorphism
of the first-stage witness B₀ is then converted into the actual full
finite graph automorphism group element used as the language component
of every second-stage auxiliary Γ-root partial automorphism.

This module proves BOTH of the public coherent-selector obligations
at the level of those real B₀ GRAPH GROUP ELEMENTS, not merely
abstractly on the successor automorphisms:

* Equivalent d-partial automorphisms select literally the same g∈Aut(B₀),
  independent of irrelevant outside-domain totalization.
* For any true original coherent triple p,q,r, the actual selected
  graph automorphisms satisfy g_r = g_q * g_p in this order.

No arbitrary lift of a symbol permutation, no global invariance of the
original source subset, and no misapplication of the unary theorem
to higher-arity d-functions is involved. The induced auxiliary root
partial-map naturality and final reconstructed witness extension
remain separate steps.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The actual first selected GRAPH automorphism depends only on the
mathematical original d-partial map, not on irrelevant PartialEquiv
fallback values outside its exact closed source domain. -/
theorem firstStage_coherentSelector_graphAut_respectsEquivalent
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (p q : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    graphAutOfSuccessorAut G
      (s.extension (dPartialAutomorphism_to_successor A k p)) =
    graphAutOfSuccessorAut G
      (s.extension (dPartialAutomorphism_to_successor A k q)) := by
  exact congrArg (graphAutOfSuccessorAut G)
    (s.respects_equivalent
      (dPartialAutomorphism_to_successor A k p)
      (dPartialAutomorphism_to_successor A k q)
      (dPartialAutomorphism_to_successor_equivalent A k p q hpq))

/-- Selection of the actual full graph automorphism of B₀
respects every coherent triple of source partial automorphisms
in the ORIGINAL complete d-language (including every F_n).
The group product is precisely the auxiliary language action
group's multiplication g_q*g_p, with no posthoc choice of lifts. -/
theorem firstStage_coherentSelector_graphAut_coherentTriple
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (p q r : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (hTriple : Structure.PartialIsomorphism.CoherentTriple p q r) :
    graphAutOfSuccessorAut G
      (s.extension (dPartialAutomorphism_to_successor A k r)) =
    graphAutOfSuccessorAut G
      (s.extension (dPartialAutomorphism_to_successor A k q)) *
    graphAutOfSuccessorAut G
      (s.extension (dPartialAutomorphism_to_successor A k p)) := by
  have hs : s.extension (dPartialAutomorphism_to_successor A k r) =
      (s.extension (dPartialAutomorphism_to_successor A k q)).comp
        (s.extension (dPartialAutomorphism_to_successor A k p)) :=
    s.coherent
      (dPartialAutomorphism_to_successor A k p)
      (dPartialAutomorphism_to_successor A k q)
      (dPartialAutomorphism_to_successor A k r)
      (dPartialAutomorphism_to_successor_coherentTriple A k p q r hTriple)
  calc
    graphAutOfSuccessorAut G
        (s.extension (dPartialAutomorphism_to_successor A k r)) =
      graphAutOfSuccessorAut G
        ((s.extension (dPartialAutomorphism_to_successor A k q)).comp
          (s.extension (dPartialAutomorphism_to_successor A k p))) :=
      congrArg (graphAutOfSuccessorAut G) hs
    _ = graphAutOfSuccessorAut G
          (s.extension (dPartialAutomorphism_to_successor A k q)) *
        graphAutOfSuccessorAut G
          (s.extension (dPartialAutomorphism_to_successor A k p)) :=
      graphAutOfSuccessorAut_comp G
        (s.extension (dPartialAutomorphism_to_successor A k q))
        (s.extension (dPartialAutomorphism_to_successor A k p))

end AllThoseEPPA.Applications.KOrientations
