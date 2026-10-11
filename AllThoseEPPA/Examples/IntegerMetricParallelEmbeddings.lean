import AllThoseEPPA.Examples.IntegerMetricBridge
import Lean.Elab.Tactic.Omega

/-!
# Distance agreement on a common relational substructure

Suppose an arbitrary partial D-distance-colour structure Q embeds
EXACTLY into the complete distance-colour encodings of two bounded
integer metric spaces X and Y. Then the two embeddings necessarily
induce exactly the SAME metric on Q.

This observation avoids making Q itself an explicit member of the
metric class at the interface of the manuscript's amalgamation API:
amalgamation of two metric members is requested along an arbitrary
exactly embedded structure Q, not necessarily a member of the class.
The result furnishes the common real metric required by GlueSpace.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u v w

/-- Exact relational embeddings of a common arbitrary partial
binary structure into two complete D-metrics induce identical
metric distances on every pair of points in their common source.
No finiteness or positivity condition on D is required. -/
theorem parallelMetricEmbeddings_dist_agree
    {D : ℕ} {I : Type u} {V : Type v} {W : Type w}
    (Q : Structure (language D) I)
    (M : BoundedNatMetric D V)
    (N : BoundedNatMetric D W)
    (f : Structure.Embedding (action D) Q (toStructure M))
    (g : Structure.Embedding (action D) Q (toStructure N))
    (x y : I) :
    M.dist (f x) (f y) = N.dist (g x) (g y) := by
  by_cases hxy : x = y
  · subst y
    rw [M.toNatMetric.dist_self, N.toNatMetric.dist_self]
  · have hDistinct : f x ≠ f y := f.injective.ne hxy
    have hPos : 0 < M.dist (f x) (f y) :=
      M.toNatMetric.dist_pos hDistinct
    have hBound : M.dist (f x) (f y) ≤ D :=
      M.dist_le (f x) (f y)
    let d : Fin D := ⟨M.dist (f x) (f y) - 1, by omega⟩
    have hInM : (toStructure M).rel
        (RelSymbol.edge d) ![f x, f y] := by
      change M.dist (f x) (f y) =
        M.dist (f x) (f y) - 1 + 1
      omega
    have hOld : Q.rel (RelSymbol.edge d) ![x,y] := by
      have ht : (f.toFun ∘ (![x,y] : Fin 2 → I)) =
          (![f x,f y] : Fin 2 → V) := by
        funext i
        fin_cases i <;> rfl
      have hf := f.map_rel_iff (RelSymbol.edge d) ![x,y]
      simp only [action_on_edge, ht] at hf
      exact hf.mp hInM
    have hInN : (toStructure N).rel
        (RelSymbol.edge d) ![g x, g y] := by
      have ht : (g.toFun ∘ (![x,y] : Fin 2 → I)) =
          (![g x,g y] : Fin 2 → W) := by
        funext i
        fin_cases i <;> rfl
      have hg := g.map_rel_iff (RelSymbol.edge d) ![x,y]
      simp only [action_on_edge, ht] at hg
      exact hg.mpr hOld
    change N.dist (g x) (g y) =
      M.dist (f x) (f y) - 1 + 1 at hInN
    omega

end Bridge
end IntegerMetric
end AllThoseEPPA
