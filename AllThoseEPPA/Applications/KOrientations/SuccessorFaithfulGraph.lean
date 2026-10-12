import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases
import AllThoseEPPA.Applications.KOrientations.FaithfulLocalTransfer
import AllThoseEPPA.Applications.KOrientations.Encoding
import AllThoseEPPA.Automorphism

/-!
# The edge graph of a faithful first-stage witness is oriented

An unrestricted EPPA witness need not satisfy the intended graph
axioms automatically. Here irreducible-structure faithfulness
transports the closure of every realized directed edge into the
distinguished original graph. Since the source has no antiparallel
edges, neither can the witness.

This constructs an actual \`Digraph\` from the raw first-stage
\`Structure successorLanguage\`. The outdegree bound and exact
successor-function interpretation are separate later obligations.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The edge symbol is fixed by the trivial language action. -/
@[simp] theorem successorAction_on_edge (g : PUnit) :
    successorAction.onRel g EdgeSymbol.edge = EdgeSymbol.edge := by
  rfl

/-- An edge in a faithful successor-language witness can be moved
onto a real edge of the distinguished source graph. -/
theorem faithful_edgeTuple_movable
    {α : Type u} {β : Type v}
    (G : Digraph α) (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι)
    {x y : β} (hEdge : B.rel EdgeSymbol.edge ![x, y]) :
    ∃ (g : Structure.Automorphism successorAction B)
      (a b : α),
      g x = ι a ∧ g y = ι b ∧ G.edge a b := by
  classical
  let xs : Fin 2 → β := ![x, y]
  obtain ⟨g, hmove⟩ :=
    faithful_moves_relationClosure successorAction
      (successorStructure G) B ι hFaith EdgeSymbol.edge xs hEdge
  have hx : x ∈ B.closureSet (Set.range xs) :=
    B.subset_closureSet (Set.range xs) ⟨0, rfl⟩
  have hy : y ∈ B.closureSet (Set.range xs) :=
    B.subset_closureSet (Set.range xs) ⟨1, rfl⟩
  obtain ⟨a, ha⟩ := hmove x hx
  obtain ⟨b, hb⟩ := hmove y hy
  have hg : B.rel EdgeSymbol.edge (g ∘ xs) := by
    simpa only [successorAction_on_edge] using
      ((Structure.Automorphism.map_rel_iff
        g EdgeSymbol.edge xs).2 hEdge)
  have htuple : (g ∘ xs) = (ι.toFun ∘ ![a, b]) := by
    funext i
    fin_cases i
    · simpa [xs, Function.comp_def] using ha
    · simpa [xs, Function.comp_def] using hb
  rw [htuple] at hg
  have hA : (successorStructure G).rel
      EdgeSymbol.edge ![a, b] := by
    apply (ι.map_rel_iff EdgeSymbol.edge ![a, b]).1
    simpa only [successorAction_on_edge] using hg
  exact ⟨g, a, b, ha, hb, hA⟩

/-- Faithfulness excludes antiparallel edges and loops in the raw
first-stage witness. -/
theorem faithful_edge_asymm
    {α : Type u} {β : Type v}
    (G : Digraph α) (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι)
    {x y : β} (hxy : B.rel EdgeSymbol.edge ![x, y]) :
    ¬ B.rel EdgeSymbol.edge ![y, x] := by
  intro hyx
  obtain ⟨g, a, b, ha, hb, hab⟩ :=
    faithful_edgeTuple_movable G B ι hFaith hxy
  let xs : Fin 2 → β := ![y, x]
  have hg : B.rel EdgeSymbol.edge (g ∘ xs) := by
    simpa only [successorAction_on_edge] using
      ((Structure.Automorphism.map_rel_iff
        g EdgeSymbol.edge xs).2 hyx)
  have htuple : (g ∘ xs) = (ι.toFun ∘ ![b, a]) := by
    funext i
    fin_cases i
    · simpa [xs, Function.comp_def] using hb
    · simpa [xs, Function.comp_def] using ha
  rw [htuple] at hg
  have hba : G.edge b a := by
    have hA : (successorStructure G).rel
        EdgeSymbol.edge ![b, a] := by
      apply (ι.map_rel_iff EdgeSymbol.edge ![b, a]).1
      simpa only [successorAction_on_edge] using hg
    exact hA
  exact (G.asymmetric hab) hba

/-- The raw faithful witness's binary relation defines a genuine
oriented graph even before checking its outdegree or unary function. -/
def faithfulWitnessDigraph
    {α : Type u} {β : Type v}
    (G : Digraph α) (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι) :
    Digraph β where
  edge x y := B.rel EdgeSymbol.edge ![x, y]
  asymmetric := by
    intro x y hxy
    exact faithful_edge_asymm G B ι hFaith hxy

end AllThoseEPPA.Applications.KOrientations
