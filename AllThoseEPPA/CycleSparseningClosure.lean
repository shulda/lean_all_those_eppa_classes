import AllThoseEPPA.CycleSparseningFinite

/-!
# Closure calculus for the cycle-sparsening witness

The proof of Claim `c:cycles:irreducible` is the same closure argument as in
the faithful construction.  This file establishes the corresponding closure
calculus for cycle valuation structures.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {V : Type v}
variable (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Restricting a valuation structure at its own centre changes nothing. -/
theorem ValuationStructure.restrict_self
    {x : V} (W : ValuationStructure B₀ E x) :
    W.restrict B₀ E x (B₀.mem_closureAtSet x) = W := by
  apply Subtype.ext
  funext t
  change
    W.1 (closureInclusion B₀ (B₀.mem_closureAtSet x) t) =
      W.1 t
  have ht :
      closureInclusion B₀ (B₀.mem_closureAtSet x) t = t := by
    apply Subtype.ext
    rfl
  cases ht
  rfl

/-- Restriction to nested one-point closures is transitive. -/
theorem ValuationStructure.restrict_trans
    {x y z : V}
    (W : ValuationStructure B₀ E x)
    (hy : y ∈ B₀.closureAtSet x)
    (hz : z ∈ B₀.closureAtSet y) :
    (W.restrict B₀ E y hy).restrict B₀ E z hz =
      W.restrict B₀ E z
        (B₀.closureAtSet_subset_of_mem hy hz) := by
  apply Subtype.ext
  funext t
  change
    W.1
        (closureInclusion B₀ hy
          (closureInclusion B₀ hz t)) =
      W.1
        (closureInclusion B₀
          (B₀.closureAtSet_subset_of_mem hy hz) t)
  have ht :
      closureInclusion B₀ hy (closureInclusion B₀ hz t) =
        closureInclusion B₀
          (B₀.closureAtSet_subset_of_mem hy hz) t := by
    apply Subtype.ext
    rfl
  cases ht
  rfl

/-- The witness vertex obtained by restricting a valuation structure to a
point of its base closure. -/
def restrictionVertex
    (w : WitnessVertex B₀ E)
    (y : V) (hy : y ∈ B₀.closureAtSet (WitnessVertex.base B₀ E w)) :
    WitnessVertex B₀ E :=
  ⟨y, (WitnessVertex.valuation B₀ E w).restrict B₀ E y hy⟩

@[simp] theorem restrictionVertex_base
    (w : WitnessVertex B₀ E)
    (y : V) (hy : y ∈ B₀.closureAtSet (WitnessVertex.base B₀ E w)) :
    WitnessVertex.base B₀ E (restrictionVertex B₀ E w y hy) = y :=
  rfl

/-- Restricting at the base point returns the original witness vertex. -/
theorem restrictionVertex_self
    (w : WitnessVertex B₀ E) :
    restrictionVertex B₀ E w (WitnessVertex.base B₀ E w)
        (B₀.mem_closureAtSet (WitnessVertex.base B₀ E w)) = w := by
  rcases w with ⟨x, W⟩
  apply Sigma.ext rfl
  exact heq_of_eq
    (ValuationStructure.restrict_self B₀ E W)

/-- Restricting a restricted witness vertex is the same as restricting the
original vertex directly. -/
theorem restrictionVertex_trans
    (w : WitnessVertex B₀ E)
    {y z : V}
    (hy : y ∈ B₀.closureAtSet (WitnessVertex.base B₀ E w))
    (hz : z ∈ B₀.closureAtSet y) :
    restrictionVertex B₀ E
        (restrictionVertex B₀ E w y hy) z hz =
      restrictionVertex B₀ E w z
        (B₀.closureAtSet_subset_of_mem hy hz) := by
  apply Sigma.ext rfl
  exact heq_of_eq
    (ValuationStructure.restrict_trans B₀ E
      (WitnessVertex.valuation B₀ E w) hy hz)

/-- A unary function-value vertex of a restricted vertex is the direct
restriction of the original witness vertex at that function value. -/
theorem functionValueVertex_restrictionVertex
    (w : WitnessVertex B₀ E)
    {y z : V}
    (hy : y ∈ B₀.closureAtSet (WitnessVertex.base B₀ E w))
    {n : ℕ} (F : L.FuncSymbol n)
    (hz : z ∈ B₀.func F (fun _ => y)) :
    functionValueVertex B₀ E
        (restrictionVertex B₀ E w y hy)
        F z hz =
      restrictionVertex B₀ E w z
        (B₀.closureAtSet_subset_of_mem hy
          (func_mem_closureAtSet B₀ F hz)) := by
  simpa [functionValueVertex, restrictionVertex,
    WitnessVertex.valuation, WitnessVertex.base] using
    (restrictionVertex_trans B₀ E w hy
      (func_mem_closureAtSet B₀ F hz))

/-- A descendant of `w` is obtained by restricting `w` to a point of its
base one-point closure. -/
def IsDescendant
    (w z : WitnessVertex B₀ E) : Prop :=
  ∃ (y : V)
    (hy : y ∈ B₀.closureAtSet (WitnessVertex.base B₀ E w)),
    z = restrictionVertex B₀ E w y hy

/-- Descendants of a witness vertex form a function-closed subset. -/
theorem descendants_isClosed
    (w : WitnessVertex B₀ E) :
    (witnessStructure B₀ E).IsClosed
      {z | IsDescendant B₀ E w z} := by
  intro n F xs hxs z hz
  let i := UnaryFunctions.unaryIndex F
  have huDesc : IsDescendant B₀ E w (xs i) :=
    hxs i
  rcases huDesc with ⟨y, hy, huy⟩
  have hconst :
      xs = fun _ => restrictionVertex B₀ E w y hy := by
    calc
      xs = fun _ => xs i := by
        simpa [i] using
          (UnaryFunctions.unaryTuple_eq_constant F xs)
      _ = fun _ => restrictionVertex B₀ E w y hy := by
        funext j
        exact huy
  rw [hconst] at hz
  change
    ∃ (t : V)
      (ht : t ∈ B₀.func F
        (fun _ =>
          WitnessVertex.base B₀ E
            (restrictionVertex B₀ E w y hy))),
      z =
        functionValueVertex B₀ E
          (restrictionVertex B₀ E w y hy) F t ht at hz
  rcases hz with ⟨t, ht, hzt⟩
  subst z
  have ht' : t ∈ B₀.func F (fun _ => y) := by
    simpa using ht
  let htcl : t ∈ B₀.closureAtSet (WitnessVertex.base B₀ E w) :=
    B₀.closureAtSet_subset_of_mem hy
      (func_mem_closureAtSet B₀ F ht')
  refine ⟨t, htcl, ?_⟩
  simpa [htcl] using
    (functionValueVertex_restrictionVertex
      B₀ E w hy F ht')

/-- The witness closure of a vertex is contained in its descendants. -/
theorem closureAtSet_subset_descendants
    (w : WitnessVertex B₀ E) :
    (witnessStructure B₀ E).closureAtSet w ⊆
      {z | IsDescendant B₀ E w z} := by
  apply
    (witnessStructure B₀ E).closureSet_minimal
      (descendants_isClosed B₀ E w)
  intro z hz
  have hzw : z = w := by simpa using hz
  subst z
  refine
    ⟨WitnessVertex.base B₀ E w,
      B₀.mem_closureAtSet (WitnessVertex.base B₀ E w), ?_⟩
  exact (restrictionVertex_self B₀ E w).symm

end Sparsening
end AllThoseEPPA
