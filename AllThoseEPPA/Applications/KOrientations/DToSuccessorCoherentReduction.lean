import AllThoseEPPA.Applications.KOrientations.DToSuccessorPartialAutomorphism

/-!
# Coherent-triple naturality of the exact d-to-successor partial-map reduct

A source full d-closure partial automorphism has a genuine partial
equivalence with a precisely specified source and target. Forgetting
the arbitrary-arity root-fibre functions leaves its PartialEquiv
UNCHANGED: the reduction is an actual map of partial-map groupoids.

In particular, the reduction preserves the public library's
PartialIsomorphism.Equivalent and CoherentTriple predicates,
which identify partial maps modulo irrelevant outside-domain
totalization, not by raw equality of the Lean PartialEquiv structs.

The unary-successor and full-d language actions are both trivial;
the language-group equality here is supplied by subsingletonness of
PUnit, not an arbitrary choice of a symbol-image lift. This is
precisely the coherent source-reduction interface used by the
first stage in the two-stage k-orientation construction. It does
NOT yet prove existence of a coherent final extension.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- Equivalent mathematical partial automorphisms of the full
d-expansion induce equivalent partial automorphisms of the
unary-successor reduct, with exactly the same domains and maps. -/
theorem dPartialAutomorphism_to_successor_equivalent
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (p q : Structure.PartialAutomorphism dTrivialAction (dStructure G k))
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    Structure.PartialIsomorphism.Equivalent
      (dPartialAutomorphism_to_successor G k p)
      (dPartialAutomorphism_to_successor G k q) := by
  refine ⟨Subsingleton.elim _ _, ?_⟩
  exact hpq.2

/-- Exact composability and the entire coherent-triple relation
survive forgetting the higher-arity d-fibre symbols. This is
stronger than mere preservation of pointwise partial extension. -/
theorem dPartialAutomorphism_to_successor_coherentTriple
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (p q r : Structure.PartialAutomorphism dTrivialAction (dStructure G k))
    (hC : Structure.PartialIsomorphism.CoherentTriple p q r) :
    Structure.PartialIsomorphism.CoherentTriple
      (dPartialAutomorphism_to_successor G k p)
      (dPartialAutomorphism_to_successor G k q)
      (dPartialAutomorphism_to_successor G k r) := by
  obtain ⟨hPQ, hEq⟩ := hC
  refine ⟨hPQ, ?_⟩
  refine ⟨Subsingleton.elim _ _, ?_⟩
  exact hEq.2

end AllThoseEPPA.Applications.KOrientations
