import AllThoseEPPA.Applications.KOrientations.FirstStageInClass
import AllThoseEPPA.Applications.KOrientations.SuccessorFaithfulFunctions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# The embedded original source is successor-closed

The first stage uses an *exact embedding* of the original successor
expansion into B₀. The unary successor function is the complete
directed reachable set, and exact function preservation forces the
image of the old vertex set to contain every vertex reachable from
one of its elements.

This discharges, for the actual first-stage source S, the
successor-closed hypothesis appearing in the later pattern-lifting
lemma; no hypothesis that all of B₀ is rooted is needed.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The source copy of an exact successor-language embedding is
closed under every directed path of the target graph. -/
theorem successorEmbedding_image_successorClosed
    {U : Type u} {V : Type v}
    (A : Digraph U) (G : Digraph V)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G)) :
    ∀ x y : V, x ∈ Set.range ι.toFun →
      G.Reaches x y → y ∈ Set.range ι.toFun := by
  intro x y hx hxy
  obtain ⟨a, rfl⟩ := hx
  have hMap := ι.map_func SuccessorSymbol.successor ![a]
  have htup : (ι.toFun ∘ ![a]) = ![ι a] := by
    funext i
    fin_cases i
    rfl
  rw [htup] at hMap
  have hEq : Structure.imageSet ι.toFun (A.successors a) =
      G.successors (ι a) := by
    simpa only [successorStructure_successors,
      successorAction_on_func] using hMap
  have hy : y ∈ G.successors (ι a) := hxy
  rw [← hEq] at hy
  obtain ⟨b, _, hb⟩ := hy
  exact ⟨b, hb⟩

/-- In particular, the image is an honest closed substructure of the
successor-language encoding of the target graph. -/
theorem successorEmbedding_image_isClosed
    {U : Type u} {V : Type v}
    (A : Digraph U) (G : Digraph V)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G)) :
    (successorStructure G).IsClosed (Set.range ι.toFun) := by
  apply (successorStructure_isClosed_iff G (Set.range ι.toFun)).2
  exact successorEmbedding_image_successorClosed A G ι

end AllThoseEPPA.Applications.KOrientations
