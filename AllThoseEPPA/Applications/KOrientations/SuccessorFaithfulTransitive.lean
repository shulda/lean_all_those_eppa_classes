import AllThoseEPPA.Applications.KOrientations.SuccessorFaithfulUnary

/-!
# The unary successor function is transitive in the faithful witness

The main nontrivial local s-closure identity. First prove transport
equivalences for the unique unary function under (i) an exact
embedding and (ii) an automorphism. Irreducible-structure faithfulness
then allows transport of an entire one-point closure into the original
successor expansion, where reachability is transitive.

This proves F(F(x)) subset F(x), not yet F(x) equal to the graph
reachability set. The converse path-lifting argument is separate.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- An exact embedding reflects as well as preserves unary function
membership between points in its source. -/
theorem embedding_successor_iff
    {α : Type u} {β : Type v}
    (G : Digraph α) (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (a b : α) :
    b ∈ G.successors a ↔
      ι b ∈ B.func SuccessorSymbol.successor ![ι a] := by
  have hmap := ι.map_func SuccessorSymbol.successor ![a]
  have htup : (ι.toFun ∘ ![a]) = ![ι a] := by
    funext i
    fin_cases i
    rfl
  rw [htup] at hmap
  have heq :
      Structure.imageSet ι.toFun (G.successors a) =
        B.func SuccessorSymbol.successor ![ι a] := by
    simpa only [successorStructure_successors,
      successorAction_on_func] using hmap
  constructor
  · intro hb
    rw [← heq]
    exact ⟨b, hb, rfl⟩
  · intro hb
    rw [← heq] at hb
    rcases hb with ⟨c, hc, hcb⟩
    have hbc : c = b := ι.injective hcb
    simpa [hbc] using hc

/-- Automorphisms transport unary function membership in both
directions, using exact set-valued function preservation. -/
theorem automorphism_successor_iff
    {β : Type v} (B : Structure successorLanguage β)
    (g : Structure.Automorphism successorAction B)
    (x y : β) :
    y ∈ B.func SuccessorSymbol.successor ![x] ↔
      g y ∈ B.func SuccessorSymbol.successor ![g x] := by
  have hmap := Structure.Automorphism.map_func
    g SuccessorSymbol.successor ![x]
  have htup : (g ∘ ![x]) = ![g x] := by
    funext i
    fin_cases i
    rfl
  rw [htup] at hmap
  have heq :
      Structure.imageSet g (B.func SuccessorSymbol.successor ![x]) =
        B.func SuccessorSymbol.successor ![g x] := by
    simpa only [successorAction_on_func] using hmap
  constructor
  · intro hy
    rw [← heq]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← heq] at hy
    rcases hy with ⟨z, hz, hzy⟩
    have hzy' : z = y := g.toEquiv.injective hzy
    simpa [hzy'] using hz

/-- In a faithful unary witness, the successor function is
transitively closed: y∈F(x), z∈F(y) implies z∈F(x). -/
theorem faithful_successor_trans
    {α : Type u} {β : Type v}
    (G : Digraph α) (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι)
    {x y z : β}
    (hxy : y ∈ B.func SuccessorSymbol.successor ![x])
    (hyz : z ∈ B.func SuccessorSymbol.successor ![y]) :
    z ∈ B.func SuccessorSymbol.successor ![x] := by
  have hycl : y ∈ B.closureAtSet x :=
    successorValue_subset_closureAt B x hxy
  have hzcl : z ∈ B.closureAtSet x :=
    (B.closureAtSet_subset_of_mem hycl)
      (successorValue_subset_closureAt B y hyz)
  obtain ⟨g, hmove⟩ :=
    faithful_moves_vertexClosure successorAction
      (successorStructure G) B ι hFaith x
  obtain ⟨a, ha⟩ := hmove x (B.mem_closureAtSet x)
  obtain ⟨b, hb⟩ := hmove y hycl
  obtain ⟨c, hc⟩ := hmove z hzcl
  have hxyg : g y ∈ B.func SuccessorSymbol.successor ![g x] :=
    (automorphism_successor_iff B g x y).mp hxy
  have hyzg : g z ∈ B.func SuccessorSymbol.successor ![g y] :=
    (automorphism_successor_iff B g y z).mp hyz
  have hab : b ∈ G.successors a := by
    apply (embedding_successor_iff G B ι a b).mpr
    simpa only [ha, hb] using hxyg
  have hbc : c ∈ G.successors b := by
    apply (embedding_successor_iff G B ι b c).mpr
    simpa only [hb, hc] using hyzg
  have hac : c ∈ G.successors a :=
    G.reaches_trans hab hbc
  have hxzg : g z ∈ B.func SuccessorSymbol.successor ![g x] := by
    have h := (embedding_successor_iff G B ι a c).mp hac
    simpa only [ha, hc] using h
  exact (automorphism_successor_iff B g x z).mpr hxzg

end AllThoseEPPA.Applications.KOrientations
