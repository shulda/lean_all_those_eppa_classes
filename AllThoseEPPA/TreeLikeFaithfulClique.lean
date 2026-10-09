import AllThoseEPPA.TreeLikeEdgeCut

/-!
# Irreducible-structure faithfulness forces local E-cliques

This connects the structural clique/cut API to the already formalized
EPPA witnesses. If E is fixed by the language relabelling group and
E is complete on the distinguished copy of A, irreducible-structure
faithfulness implies that every irreducible closed substructure of B
is an E-clique. This is the exact local hypothesis used by the
graph-separator and clique-closure lemmas for `lem:cuts`.

No extra model-theoretic or graph-theoretic assumptions are added.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w z

variable {L : Language.{u}}
variable {Γ : Type v} [Group Γ]
variable {α : Type w} {β : Type z}

/-- Irreducible structure faithfulness combined with a complete fixed
E-relation on A implies the E-clique condition for every irreducible
closed substructure of B. This is the bridge from `lem:sparsen`
to the structural part of `lem:cuts`. -/
theorem irreduciblesAreCliques_of_faithful
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ) :
    IrreduciblesAreCliques B E := by
  intro S hS hirr x y hx hy hxy
  obtain ⟨g, hg⟩ := hfaith S hS hirr
  obtain ⟨a, hga⟩ := hg x hx
  obtain ⟨b, hgb⟩ := hg y hy
  have hab : a ≠ b := by
    intro heq
    apply hxy
    apply g.toEquiv.injective
    change g x = g y
    calc
      g x = ψ a := hga
      _ = ψ b := by rw [heq]
      _ = g y := hgb.symm
  have heA : A.Edge E a b :=
    (hcomplete a b).2 hab
  have heB : B.Edge E (ψ a) (ψ b) :=
    (ψ.edge_map_iff E hfix a b).2 heA
  have heG : B.Edge E (g x) (g y) := by
    simpa only [hga, hgb] using heB
  exact (g.edge_map_iff E hfix x y).1 heG

end TreeLike
end AllThoseEPPA
