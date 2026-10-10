import AllThoseEPPA.TreeLikeEmbeddingCliqueBridge

/-!
# The distinguished E-reduct is automatically a simple graph

For Lemma `lem:cuts`, the key hypothesis is that every
irreducible substructure of B embeds into A and E is fixed by
the language action, with E a complete simple graph on A.

The graph-separator machinery assumes that E is loopless and
symmetric on B. These are **consequences**, not additional
hypotheses: any E-loop lives in the irreducible one-point
closure and therefore transfers to A; symmetry then follows
from the previously checked lemma for E-clique irreducibles.

This makes the hypothesis interface for `lem:cuts` faithful
to the statement in the manuscript.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {α : Type w} {β : Type x}

/-- Every irreducible substructure of B embeds into an E-complete A:
in particular, E has no loops anywhere in B. -/
theorem edgeLoopless_of_everyIrreducibleEmbedsIn
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (E : L.RelSymbol 2)
    (hFix : act.FixesRel E)
    (hComplete : A.EdgeComplete E)
    (hEvery : EveryIrreducibleEmbedsIn act A B) :
    B.EdgeLoopless E := by
  intro x hxx
  let S : Set β := B.closureAtSet x
  let hS : B.IsClosed S := B.isClosed_closureSet {x}
  have hIrr : (B.induce S hS).IsIrreducible :=
    B.closureAt_isIrreducible x
  obtain ⟨f⟩ := hEvery S hS hIrr
  let sx : S := ⟨x, B.mem_closureAtSet x⟩
  have hEdge : (B.induce S hS).Edge E sx sx := by
    change B.rel E (Subtype.val ∘ Structure.pairTuple sx sx)
    rw [Structure.pairTuple_map]
    exact hxx
  have hA : A.Edge E (f sx) (f sx) :=
    (f.edge_map_iff E hFix sx sx).2 hEdge
  exact ((hComplete (f sx) (f sx)).mp hA) rfl

/-- The same local embedding hypothesis implies symmetry of the
distinguished relation. This uses no separately assumed graph
symmetry on B. -/
theorem edgeSymmetric_of_everyIrreducibleEmbedsIn
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (E : L.RelSymbol 2)
    (hFix : act.FixesRel E)
    (hComplete : A.EdgeComplete E)
    (hEvery : EveryIrreducibleEmbedsIn act A B) :
    B.EdgeSymmetric E :=
  edgeSymmetric_of_irreducibleCliques B E
    (irreduciblesAreCliques_of_everyIrreducibleEmbedsIn
      act A B E hFix hComplete hEvery)
    (edgeLoopless_of_everyIrreducibleEmbedsIn
      act A B E hFix hComplete hEvery)

end TreeLike
end AllThoseEPPA
