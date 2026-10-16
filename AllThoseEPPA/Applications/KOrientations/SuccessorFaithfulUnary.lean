import AllThoseEPPA.Applications.KOrientations.SuccessorFaithfulFunctions

/-!
# Reflexive unary successor sets in a faithful first-stage witness

The original successor expansion contains each vertex in its own
set-valued unary function. This is a local property of a point
closure, hence it transfers by irreducible-structure faithfulness
even though the unrestricted EPPA witness is not assumed to belong
to the successor-closure class.

The separate closure-inclusion lemma holds for every structure,
without any faithfulness hypothesis.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every value of the unary function is contained in the library's
one-point closure. No EPPA hypothesis is used here. -/
theorem successorValue_subset_closureAt
    {β : Type v} (B : Structure successorLanguage β)
    (x : β) :
    B.func SuccessorSymbol.successor ![x] ⊆
      B.closureAtSet x := by
  intro y hy
  apply (B.isClosed_closureSet {x})
      SuccessorSymbol.successor ![x]
  · intro i
    fin_cases i
    exact B.mem_closureAtSet x
  · exact hy

/-- In a faithful successor-language witness, every vertex is an
element of its own successor-function value. -/
theorem faithful_successor_self
    {α : Type u} {β : Type v}
    (G : Digraph α) (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι)
    (x : β) :
    x ∈ B.func SuccessorSymbol.successor ![x] := by
  obtain ⟨g, hg⟩ :=
    faithful_moves_vertexClosure
      successorAction (successorStructure G) B ι hFaith x
  obtain ⟨a, ha⟩ := hg x (B.mem_closureAtSet x)
  have haMem : a ∈ G.successors a :=
    G.self_mem_successors a
  have himage :
      ι a ∈ Structure.imageSet ι.toFun
          ((successorStructure G).func SuccessorSymbol.successor ![a]) :=
    ⟨a, haMem, rfl⟩
  have hι := ι.map_func SuccessorSymbol.successor ![a]
  rw [hι] at himage
  have htuple : (ι.toFun ∘ ![a]) = ![g x] := by
    funext i
    fin_cases i
    simpa [Function.comp_def] using ha.symm
  rw [htuple] at himage
  have hgself :
      g x ∈ B.func SuccessorSymbol.successor ![g x] := by
    simpa only [ha, successorAction_on_func] using himage

  have hmap := Structure.Automorphism.map_func
    g SuccessorSymbol.successor ![x]
  have htupleG : (g ∘ ![x]) = ![g x] := by
    funext i
    fin_cases i
    rfl
  rw [htupleG] at hmap
  have hmap' :
      Structure.imageSet g (B.func SuccessorSymbol.successor ![x]) =
        B.func SuccessorSymbol.successor ![g x] := by
    simpa only [successorAction_on_func] using hmap
  have himageG :
      g x ∈ Structure.imageSet g
        (B.func SuccessorSymbol.successor ![x]) := by
    rw [hmap']
    exact hgself
  rcases himageG with ⟨y, hy, hgy⟩
  have heq : y = x := g.toEquiv.injective hgy
  simpa [heq] using hy

end AllThoseEPPA.Applications.KOrientations
