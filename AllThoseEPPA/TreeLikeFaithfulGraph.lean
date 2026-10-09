import AllThoseEPPA.TreeLikeFaithfulClique

/-!
# The distinguished relation is a simple graph on a faithful witness

The clique-cut lemma uses an undirected simple E-graph. The paper starts
with an E-clique in A and the faithful cycle-sparsening machinery, but
does not add a separate symmetry or looplessness assumption on the
resulting witness. We establish these consequences explicitly here.

The proof uses two already checked facts:
* every one-point closure is irreducible, so faithfulness precludes E-loops;
* the closure of any realized relation tuple is irreducible, so local
  irreducible E-cliques force E-edges to be symmetric.

Together with the separator-to-free-decomposition lemma, this closes
the structural (nonchordal) half of a single clique cut.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w z
variable {L : Language.{u}}
variable {Γ : Type v} [Group Γ]
variable {α : Type w} {β : Type z}

/-- Irreducible structure faithfulness and the fact that E is loopless
on the distinguished copy rule out E-loops anywhere in B. -/
theorem edgeLoopless_of_faithful
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ) :
    B.EdgeLoopless E := by
  intro x hloop
  let S : Set β := B.closureAtSet x
  have hS : B.IsClosed S := B.isClosed_closureSet {x}
  have hirr : (B.induce S hS).IsIrreducible :=
    B.closureAt_isIrreducible x
  obtain ⟨g, hg⟩ := hfaith S hS hirr
  obtain ⟨a, ha⟩ := hg x (B.mem_closureAtSet x)
  have heG : B.Edge E (g x) (g x) :=
    (g.edge_map_iff E hfix x x).2 hloop
  have heψ : B.Edge E (ψ a) (ψ a) := by
    simpa only [ha] using heG
  have heA : A.Edge E a a :=
    (ψ.edge_map_iff E hfix a a).1 heψ
  exact ((hcomplete a a).mp heA) rfl

/-- An E-loopless structure whose irreducible substructures are
E-cliques has symmetric E-edges. Both directions use the
irreducible closure of the realized E-edge tuple. -/
theorem edgeSymmetric_of_irreducibleCliques
    (B : Structure L β) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    (hloop : B.EdgeLoopless E) :
    B.EdgeSymmetric E := by
  intro x y
  constructor
  · intro hxy
    have hne : y ≠ x := by
      intro heq
      subst y
      exact hloop x hxy
    have hneTuple :
        Structure.pairTuple x y (1 : Fin 2) ≠
          Structure.pairTuple x y (0 : Fin 2) := by
      simpa using hne
    have hrel : B.rel E (Structure.pairTuple x y) := hxy
    simpa using
      (relation_tuple_edge B E hIrred E
        (Structure.pairTuple x y) hrel (1 : Fin 2) (0 : Fin 2) hneTuple)
  · intro hyx
    have hne : x ≠ y := by
      intro heq
      subst y
      exact hloop x hyx
    have hneTuple :
        Structure.pairTuple y x (1 : Fin 2) ≠
          Structure.pairTuple y x (0 : Fin 2) := by
      simpa using hne
    have hrel : B.rel E (Structure.pairTuple y x) := hyx
    simpa using
      (relation_tuple_edge B E hIrred E
        (Structure.pairTuple y x) hrel (1 : Fin 2) (0 : Fin 2) hneTuple)

/-- Consequently, E is a symmetric simple graph on an
irreducible-structure faithful witness whenever E is a complete
fixed graph on A. -/
theorem edgeSymmetric_of_faithful
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ) :
    B.EdgeSymmetric E :=
  edgeSymmetric_of_irreducibleCliques B E
    (irreduciblesAreCliques_of_faithful
      act A B ψ E hfix hcomplete hfaith)
    (edgeLoopless_of_faithful
      act A B ψ E hfix hcomplete hfaith)

/-- Paper-facing form of the structural graph-cut lemma:
on a faithful witness, a closed separator and an E-cut give an
actual free decomposition of the whole structure. -/
theorem freeDecomposition_of_faithful_edge_separator
    [L.HasUnaryFunctions]
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ)
    (X Y : Set β)
    (hcover : X ∪ Y = Set.univ)
    (hinter : B.IsClosed (X ∩ Y))
    (hcross : ∀ (x : β), x ∈ X → x ∉ Y →
      ∀ (y : β), y ∈ Y → y ∉ X → ¬ B.Edge E x y)
    (hXproper : X ≠ Set.univ) (hYproper : Y ≠ Set.univ) :
    B.FreeDecomposition :=
  freeDecomposition_of_closed_edge_separator B E
    (irreduciblesAreCliques_of_faithful
      act A B ψ E hfix hcomplete hfaith)
    (edgeSymmetric_of_faithful
      act A B ψ E hfix hcomplete hfaith)
    X Y hcover hinter hcross hXproper hYproper

end TreeLike
end AllThoseEPPA
