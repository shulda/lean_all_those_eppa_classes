import AllThoseEPPA.Applications.KOrientations.AuxiliaryLanguage
import AllThoseEPPA.Applications.KOrientations.SecondStageRootTupleClosed
import AllThoseEPPA.Applications.KOrientations.ClosedChartCover

/-!
# The original root sort is a closed substructure of B₁

The full image of the root-only source under its genuine embedding
into the second-stage witness B₁ is closed under the unary auxiliary
function. This is an exact consequence of the embedding's
set-valued-function equality, not a free amalgamation assumption.

It allows us to designate the root-supported part of the
reconstruction lying over the original source as the canonical
d-closed copy A', and to identify its root trace exactly.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The image of the entire auxiliary root source is function-closed
inside B₁. This requires exact `Embedding.map_func`, not merely
homomorphic preservation of function values. -/
theorem auxiliaryRootEmbedding_image_isClosed
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B) :
    B.IsClosed (Set.range ι.toFun) := by
  intro n F xs hxs y hy
  cases F with
  | successor =>
      obtain ⟨a, ha⟩ := hxs 0
      have hTuple : xs = ![ι a] := by
        funext i
        fin_cases i
        exact ha.symm
      rw [hTuple] at hy
      have hMap := ι.map_func AuxiliaryFunc.successor ![a]
      have hEmbTuple : (ι.toFun ∘ ![a]) = ![ι a] := by
        funext i
        fin_cases i
        rfl
      rw [hEmbTuple] at hMap
      have hEq :
          Structure.imageSet ι.toFun
              ((auxiliaryRootStructure G k S).func
                AuxiliaryFunc.successor ![a]) =
            B.func AuxiliaryFunc.successor ![ι a] := by
        simpa only [auxiliaryAction_on_successor] using hMap
      rw [← hEq] at hy
      obtain ⟨t, ht, heq⟩ := hy
      exact ⟨t, heq⟩

end AllThoseEPPA.Applications.KOrientations
