import AllThoseEPPA.Examples.IntegerMetricBridge
import Lean.Elab.Tactic.Omega

/-!
# Exact relational embeddings preserve bounded integer distances

A necessary bridge from the paper's Γ-amalgamation interface
back to ordinary metric amalgamation: any exact embedding
between complete distance-coloured encodings is automatically
an isometric embedding of the original integer metric spaces.

The alphabet can be empty (D=0), the carriers can be empty,
and no finiteness of the carrier types is required.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u v

/-- The point map of any genuine relational embedding of
bounded metric encodings preserves each original distance
EXACTLY, for all D (including zero). -/
theorem distance_preserved_by_encoding_embedding
    {D : ℕ} {V : Type u} {W : Type v}
    (A : BoundedNatMetric D V)
    (B : BoundedNatMetric D W)
    (e : Structure.Embedding (action D)
      (toStructure A) (toStructure B))
    (x y : V) :
    B.dist (e x) (e y) = A.dist x y := by
  by_cases hxy : x = y
  · subst y
    rw [A.toNatMetric.dist_self, B.toNatMetric.dist_self]
  · have hPos : 0 < A.dist x y :=
      A.toNatMetric.dist_pos hxy
    have hBound : A.dist x y ≤ D := A.dist_le x y
    let d : Fin D := ⟨A.dist x y - 1, by omega⟩
    have hOld : (toStructure A).rel (RelSymbol.edge d) ![x,y] := by
      change A.dist x y = d.val + 1
      change A.dist x y = A.dist x y - 1 + 1
      omega
    have hTarget :=
      (e.map_rel_iff (RelSymbol.edge d) ![x,y]).mpr hOld
    change B.dist (e x) (e y) = d.val + 1 at hTarget
    omega

end Bridge
end IntegerMetric
end AllThoseEPPA
