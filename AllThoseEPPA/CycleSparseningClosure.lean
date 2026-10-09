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


/-- The restriction vertex does not depend on the proof witnessing membership
in the ambient one-point closure. -/
theorem restrictionVertex_proof_irrel
    (w : WitnessVertex B₀ E)
    (y : V)
    (hy hz :
      y ∈ B₀.closureAtSet (WitnessVertex.base B₀ E w)) :
    restrictionVertex B₀ E w y hy =
      restrictionVertex B₀ E w y hz := by
  have h : hy = hz := Subsingleton.elim _ _
  subst hz
  rfl

/-- Every restriction-descendant actually belongs to the one-point closure of
the original cycle-sparsening witness vertex. -/
theorem restrictionVertex_mem_closureAtSet
    (w : WitnessVertex B₀ E)
    (y : V)
    (hy : y ∈ B₀.closureAtSet (WitnessVertex.base B₀ E w)) :
    restrictionVertex B₀ E w y hy ∈
      (witnessStructure B₀ E).closureAtSet w := by
  let x0 : B₀.closureAtSet (WitnessVertex.base B₀ E w) :=
    ⟨WitnessVertex.base B₀ E w,
      B₀.mem_closureAtSet (WitnessVertex.base B₀ E w)⟩
  let r : B₀.closureAtSet (WitnessVertex.base B₀ E w) →
      WitnessVertex B₀ E :=
    fun z => restrictionVertex B₀ E w z.1 z.2
  let T : Set (B₀.closureAtSet (WitnessVertex.base B₀ E w)) :=
    {z | r z ∈ (witnessStructure B₀ E).closureAtSet w}
  have hTclosed :
      (B₀.closureAt (WitnessVertex.base B₀ E w)).IsClosed T := by
    intro n F zs hzs z hz
    have hconst :
        zs = fun _ => zs (UnaryFunctions.unaryIndex F) :=
      UnaryFunctions.unaryTuple_eq_constant F zs
    rw [hconst] at hz
    let u : B₀.closureAtSet (WitnessVertex.base B₀ E w) :=
      zs (UnaryFunctions.unaryIndex F)
    have hzB :
        z.1 ∈ B₀.func F (fun _ => u.1) := by
      change
        z.1 ∈ B₀.func F
          (Subtype.val ∘ (fun _ => u)) at hz
      simpa [Function.comp_def] using hz
    have hval :=
      functionValueVertex_restrictionVertex
        B₀ E w u.2 F hzB
    have hproof :
        r z =
          restrictionVertex B₀ E w z.1
            (B₀.closureAtSet_subset_of_mem u.2
              (func_mem_closureAtSet B₀ F hzB)) :=
      restrictionVertex_proof_irrel
        B₀ E w z.1 z.2
          (B₀.closureAtSet_subset_of_mem u.2
            (func_mem_closureAtSet B₀ F hzB))
    have hfun :
        r z ∈
          (witnessStructure B₀ E).func F
            (fun _ => r u) := by
      refine ⟨z.1, ?_, ?_⟩
      · simpa [r, u, restrictionVertex,
          WitnessVertex.base] using hzB
      · exact hproof.trans hval.symm
    have hu :
        r u ∈ (witnessStructure B₀ E).closureAtSet w := by
      exact hzs (UnaryFunctions.unaryIndex F)
    exact
      ((witnessStructure B₀ E).isClosed_closureSet
        ({w} : Set _))
        F (fun _ => r u) (fun _ => hu) hfun
  have hx0T : x0 ∈ T := by
    change
      restrictionVertex B₀ E w
          (WitnessVertex.base B₀ E w)
          (B₀.mem_closureAtSet (WitnessVertex.base B₀ E w)) ∈
        (witnessStructure B₀ E).closureAtSet w
    rw [restrictionVertex_self B₀ E w]
    exact (witnessStructure B₀ E).mem_closureAtSet w
  have hsub :
      (B₀.closureAt (WitnessVertex.base B₀ E w)).closureAtSet x0 ⊆ T := by
    apply
      (B₀.closureAt (WitnessVertex.base B₀ E w)).closureSet_minimal
        hTclosed
    intro z hz
    have hzx : z = x0 := by simpa using hz
    subst z
    exact hx0T
  let yy : B₀.closureAtSet (WitnessVertex.base B₀ E w) := ⟨y, hy⟩
  have hyy :
      yy ∈
        (B₀.closureAt (WitnessVertex.base B₀ E w)).closureAtSet x0 := by
    rw [Structure.closureAtSet_in_closureAt_eq_univ]
    exact Set.mem_univ yy
  exact hsub hyy

/-- Restriction-descendants are contained in the cycle-sparsening witness
closure. -/
theorem descendants_subset_closureAtSet
    (w : WitnessVertex B₀ E) :
    {z | IsDescendant B₀ E w z} ⊆
      (witnessStructure B₀ E).closureAtSet w := by
  rintro z ⟨y, hy, rfl⟩
  exact restrictionVertex_mem_closureAtSet B₀ E w y hy

/-- **Closure characterization.** One-point closure in the cycle-sparsening
witness is exactly restriction of the valuation structure along the
corresponding base one-point closure. -/
theorem closureAtSet_eq_descendants
    (w : WitnessVertex B₀ E) :
    (witnessStructure B₀ E).closureAtSet w =
      {z | IsDescendant B₀ E w z} := by
  apply Set.Subset.antisymm
  · exact closureAtSet_subset_descendants B₀ E w
  · exact descendants_subset_closureAtSet B₀ E w

/-- Any unary function value belongs to the one-point closure of its input in
the cycle-sparsening witness itself. -/
theorem witness_func_mem_closureAtSet
    {x y : WitnessVertex B₀ E}
    {n : ℕ} (F : L.FuncSymbol n)
    (hy :
      y ∈ (witnessStructure B₀ E).func F (fun _ => x)) :
    y ∈ (witnessStructure B₀ E).closureAtSet x := by
  change y ∈ (witnessStructure B₀ E).closureSet {x}
  exact
    ((witnessStructure B₀ E).isClosed_closureSet ({x} : Set _))
      F (fun _ => x)
      (fun _ => (witnessStructure B₀ E).mem_closureAtSet x)
      hy

/-- Looking at an internal valuation point after restriction is literally the
same as looking at the corresponding point of the original valuation
structure. -/
theorem restrictionVertex_pointAt
    (w : WitnessVertex B₀ E)
    {y : V}
    (hy : y ∈ B₀.closureAtSet (WitnessVertex.base B₀ E w))
    (z : B₀.closureAtSet y) :
    WitnessVertex.pointAt B₀ E
        (restrictionVertex B₀ E w y hy) z =
      WitnessVertex.pointAt B₀ E w
        (closureInclusion B₀ hy z) :=
  rfl

/-- Every valuation point of a vertex in the closure of `w` is represented
by an internal valuation point of `w`. -/
theorem pointAt_eq_ancestor_of_mem_closure
    (w x : WitnessVertex B₀ E)
    (hx : x ∈ (witnessStructure B₀ E).closureAtSet w)
    (u : B₀.closureAtSet (WitnessVertex.base B₀ E x)) :
    ∃ u' : B₀.closureAtSet (WitnessVertex.base B₀ E w),
      WitnessVertex.pointAt B₀ E x u =
        WitnessVertex.pointAt B₀ E w u' := by
  rw [closureAtSet_eq_descendants B₀ E w] at hx
  rcases hx with ⟨y, hy, rfl⟩
  exact
    ⟨closureInclusion B₀ hy u,
      restrictionVertex_pointAt B₀ E w hy u⟩

/-- Two descendants of the same cycle-sparsening witness vertex have pairwise
generic internal valuation points. -/
theorem points_generic_of_mem_closure_same_ancestor
    (w x y : WitnessVertex B₀ E)
    (hx : x ∈ (witnessStructure B₀ E).closureAtSet w)
    (hy : y ∈ (witnessStructure B₀ E).closureAtSet w)
    (u : B₀.closureAtSet (WitnessVertex.base B₀ E x))
    (v : B₀.closureAtSet (WitnessVertex.base B₀ E y)) :
    AreGeneric B₀ E
      (WitnessVertex.pointAt B₀ E x u)
      (WitnessVertex.pointAt B₀ E y v) := by
  rcases
      pointAt_eq_ancestor_of_mem_closure B₀ E w x hx u with
    ⟨u', hu⟩
  rcases
      pointAt_eq_ancestor_of_mem_closure B₀ E w y hy v with
    ⟨v', hv⟩
  rw [hu, hv]
  exact (WitnessVertex.valuation B₀ E w).2 u' v'

end Sparsening
end AllThoseEPPA
