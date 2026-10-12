import AllThoseEPPA.Applications.KOrientations.SuccessorFaithfulGraph

/-!
# Every edge of the faithful witness lies in its unary successor value

The first-stage witness is produced by the unrestricted coherent
faithful EPPA theorem. Its edge relation is now known to be
asymmetric. We next use faithfulness to show that an outgoing edge
from x to y is already contained in the one-step *set-valued*
unary successor function at x.

This is a necessary local compatibility axiom; it does not yet
claim that the successor function equals complete reachability.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

@[simp] theorem successorAction_on_func (g : PUnit) :
    successorAction.onFunc g SuccessorSymbol.successor =
      SuccessorSymbol.successor := by
  rfl

/-- A realized edge x→y in a faithful successor-language witness
forces y into the unary function-value set at x. -/
theorem faithful_edge_mem_successors
    {α : Type u} {β : Type v}
    (G : Digraph α) (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι)
    {x y : β}
    (hxy : B.rel EdgeSymbol.edge ![x, y]) :
    y ∈ B.func SuccessorSymbol.successor ![x] := by
  obtain ⟨g, a, b, ha, hb, hab⟩ :=
    faithful_edgeTuple_movable G B ι hFaith hxy
  have hA : b ∈ G.successors a :=
    G.reaches_of_edge hab

  have himage :
      ι b ∈ Structure.imageSet ι.toFun
        ((successorStructure G).func SuccessorSymbol.successor ![a]) :=
    ⟨b, hA, rfl⟩
  have hι := ι.map_func SuccessorSymbol.successor ![a]
  rw [hι] at himage
  have hι' :
      ι b ∈ B.func SuccessorSymbol.successor
        (ι.toFun ∘ ![a]) := by
    simpa only [successorAction_on_func] using himage

  have htuple1 :
      (ι.toFun ∘ ![a]) = ![g x] := by
    funext i
    fin_cases i
    simpa [Function.comp_def] using ha.symm
  rw [htuple1] at hι'
  have hgy : g y ∈ B.func SuccessorSymbol.successor ![g x] := by
    simpa only [hb] using hι'

  have hmap := Structure.Automorphism.map_func
    g SuccessorSymbol.successor ![x]
  have htuple2 :
      (g ∘ ![x]) = ![g x] := by
    funext i
    fin_cases i
    rfl
  rw [htuple2] at hmap
  have hmap' :
      Structure.imageSet g
          (B.func SuccessorSymbol.successor ![x]) =
        B.func SuccessorSymbol.successor ![g x] := by
    simpa only [successorAction_on_func] using hmap
  rw [← hmap'] at hgy
  rcases hgy with ⟨z, hz, hgz⟩
  have hzy : z = y := g.toEquiv.injective hgz
  simpa [hzy] using hz

end AllThoseEPPA.Applications.KOrientations
