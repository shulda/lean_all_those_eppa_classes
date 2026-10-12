import AllThoseEPPA.Applications.KOrientations.FaithfulReachability
import AllThoseEPPA.Applications.KOrientations.SuccessorFaithfulTransitive

/-!
# Exact reachability of the first faithful EPPA witness

Irreducible-structure faithfulness permits sending the one-point closure
of any witness vertex into the source graph. Combining this with path
transport and the exact unary-function action proves the full equality
of the witness's successor value and graph-theoretic reachability.

This is a nontrivial requirement for membership of the first witness
in the successor-closure class. The outdegree bound is treated separately.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The first-stage faithful witness interprets its unary successor
function as reflexive directed-graph reachability, with no extra
successors and no missing reachable vertices. -/
theorem faithful_successor_eq_graph_reach
    {α : Type u} {β : Type v}
    (G : Digraph α) (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι)
    (x : β) :
    B.func SuccessorSymbol.successor ![x] =
      (faithfulWitnessDigraph G B ι hFaith).successors x := by
  classical
  ext y
  constructor
  · intro hxy
    have hycl : y ∈ B.closureAtSet x :=
      successorValue_subset_closureAt B x hxy
    obtain ⟨g, hmove⟩ :=
      faithful_moves_vertexClosure successorAction
        (successorStructure G) B ι hFaith x
    obtain ⟨a, ha⟩ := hmove x (B.mem_closureAtSet x)
    obtain ⟨b, hb⟩ := hmove y hycl
    have hxyg : g y ∈
        B.func SuccessorSymbol.successor ![g x] :=
      (automorphism_successor_iff B g x y).mp hxy
    have hab : G.Reaches a b := by
      apply (embedding_successor_iff G B ι a b).mpr
      simpa only [ha, hb] using hxyg
    have habWitness :=
      faithful_reaches_of_source G B ι hFaith hab
    have habBack :=
      faithful_automorphism_reaches
        G B ι hFaith (g.symm) habWitness
    have haBack : g.symm (ι a) = x := by
      rw [← ha]
      exact Structure.Automorphism.symm_apply_apply g x
    have hbBack : g.symm (ι b) = y := by
      rw [← hb]
      exact Structure.Automorphism.symm_apply_apply g y
    change (faithfulWitnessDigraph G B ι hFaith).Reaches x y
    simpa only [haBack, hbBack] using habBack
  · intro hxy
    change (faithfulWitnessDigraph G B ι hFaith).Reaches x y at hxy
    induction hxy with
    | refl x =>
        exact faithful_successor_self G B ι hFaith x
    | step h _ ih =>
        have huv :=
          faithful_edge_mem_successors G B ι hFaith h
        exact faithful_successor_trans G B ι hFaith huv ih

end AllThoseEPPA.Applications.KOrientations
