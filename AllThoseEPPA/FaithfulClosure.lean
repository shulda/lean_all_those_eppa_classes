import AllThoseEPPA.Faithful

/-!
# Closure calculus inside the faithful witness

This file proves the closure facts used in Claim `c:faithful:irreducible`.
A point of the one-point closure of a witness vertex is precisely obtained by
restricting its valuation structure to the corresponding base point.
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)

/-- Restricting a valuation structure at its own centre changes nothing. -/
theorem ValuationStructure.restrict_self
    {x : β} (V : ValuationStructure act A B₀ ψ x) :
    V.restrict act A B₀ ψ x (B₀.mem_closureAtSet x) = V := by
  apply Subtype.ext
  funext t
  change
    V.1 (closureInclusion B₀ (B₀.mem_closureAtSet x) t) =
      V.1 t
  have ht :
      closureInclusion B₀ (B₀.mem_closureAtSet x) t = t := by
    apply Subtype.ext
    rfl
  cases ht
  rfl

/-- Restriction to nested one-point closures is transitive. -/
theorem ValuationStructure.restrict_trans
    {x y z : β}
    (V : ValuationStructure act A B₀ ψ x)
    (hy : y ∈ B₀.closureAtSet x)
    (hz : z ∈ B₀.closureAtSet y) :
    (V.restrict act A B₀ ψ y hy).restrict
        act A B₀ ψ z hz =
      V.restrict act A B₀ ψ z
        (B₀.closureAtSet_subset_of_mem hy hz) := by
  apply Subtype.ext
  funext t
  change
    V.1
        (closureInclusion B₀ hy
          (closureInclusion B₀ hz t)) =
      V.1
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
    (w : WitnessVertex act A B₀ ψ)
    (y : β) (hy : y ∈ B₀.closureAtSet w.base) :
    WitnessVertex act A B₀ ψ :=
  ⟨y, w.valuation.restrict act A B₀ ψ y hy⟩

@[simp] theorem restrictionVertex_base
    (w : WitnessVertex act A B₀ ψ)
    (y : β) (hy : y ∈ B₀.closureAtSet w.base) :
    (restrictionVertex act A B₀ ψ w y hy).base = y :=
  rfl

/-- Restricting at the base point returns the original witness vertex. -/
theorem restrictionVertex_self
    (w : WitnessVertex act A B₀ ψ) :
    restrictionVertex act A B₀ ψ w w.base
        (B₀.mem_closureAtSet w.base) = w := by
  rcases w with ⟨x, V⟩
  apply Sigma.ext rfl
  exact heq_of_eq
    (ValuationStructure.restrict_self act A B₀ ψ V)

/-- Restricting a restricted witness vertex is the same as restricting the
original vertex directly. -/
theorem restrictionVertex_trans
    (w : WitnessVertex act A B₀ ψ)
    {y z : β}
    (hy : y ∈ B₀.closureAtSet w.base)
    (hz : z ∈ B₀.closureAtSet y) :
    restrictionVertex act A B₀ ψ
        (restrictionVertex act A B₀ ψ w y hy) z hz =
      restrictionVertex act A B₀ ψ w z
        (B₀.closureAtSet_subset_of_mem hy hz) := by
  apply Sigma.ext rfl
  exact heq_of_eq
    (ValuationStructure.restrict_trans act A B₀ ψ
      w.valuation hy hz)

/-- A unary function-value vertex of a restricted vertex is the direct
restriction of the original witness vertex at that function value. -/
theorem functionValueVertex_restrictionVertex
    (w : WitnessVertex act A B₀ ψ)
    {y z : β}
    (hy : y ∈ B₀.closureAtSet w.base)
    {n : ℕ} (F : L.FuncSymbol n)
    (hz : z ∈ B₀.func F (fun _ => y)) :
    functionValueVertex act A B₀ ψ
        (restrictionVertex act A B₀ ψ w y hy)
        F z hz =
      restrictionVertex act A B₀ ψ w z
        (B₀.closureAtSet_subset_of_mem hy
          (func_mem_closureAtSet B₀ F hz)) := by
  simpa [functionValueVertex, restrictionVertex,
    WitnessVertex.valuation, WitnessVertex.base] using
    (restrictionVertex_trans act A B₀ ψ w hy
      (func_mem_closureAtSet B₀ F hz))

/-- A descendant of `w` is obtained by restricting `w` to one of the
points in its base one-point closure. -/
def IsDescendant
    (w v : WitnessVertex act A B₀ ψ) : Prop :=
  ∃ (y : β) (hy : y ∈ B₀.closureAtSet w.base),
    v = restrictionVertex act A B₀ ψ w y hy

/-- Descendants of a witness vertex form a function-closed subset. -/
theorem descendants_isClosed
    (w : WitnessVertex act A B₀ ψ) :
    (witnessStructure act A B₀ ψ).IsClosed
      {v | IsDescendant act A B₀ ψ w v} := by
  intro n F xs hxs z hz
  let i := UnaryFunctions.unaryIndex F
  have huDesc : IsDescendant act A B₀ ψ w (xs i) :=
    hxs i
  rcases huDesc with ⟨y, hy, huy⟩
  have hconst :
      xs = fun _ => restrictionVertex act A B₀ ψ w y hy := by
    calc
      xs = fun _ => xs i := by
        simpa [i] using
          (UnaryFunctions.unaryTuple_eq_constant F xs)
      _ = fun _ => restrictionVertex act A B₀ ψ w y hy := by
        funext j
        exact huy
  rw [hconst] at hz
  change
    ∃ (t : β)
      (ht : t ∈ B₀.func F
        (fun _ =>
          (restrictionVertex act A B₀ ψ w y hy).base)),
      z =
        functionValueVertex act A B₀ ψ
          (restrictionVertex act A B₀ ψ w y hy) F t ht at hz
  rcases hz with ⟨t, ht, hzt⟩
  subst z
  have ht' : t ∈ B₀.func F (fun _ => y) := by
    simpa using ht
  let htcl : t ∈ B₀.closureAtSet w.base :=
    B₀.closureAtSet_subset_of_mem hy
      (func_mem_closureAtSet B₀ F ht')
  refine ⟨t, htcl, ?_⟩
  simpa [htcl] using
    (functionValueVertex_restrictionVertex
      act A B₀ ψ w hy F ht')

/-- The faithful-witness closure of a vertex is contained in its descendants. -/
theorem closureAtSet_subset_descendants
    (w : WitnessVertex act A B₀ ψ) :
    (witnessStructure act A B₀ ψ).closureAtSet w ⊆
      {v | IsDescendant act A B₀ ψ w v} := by
  apply
    (witnessStructure act A B₀ ψ).closureSet_minimal
      (descendants_isClosed act A B₀ ψ w)
  intro v hv
  have hvw : v = w := by simpa using hv
  subst v
  refine
    ⟨w.base, B₀.mem_closureAtSet w.base, ?_⟩
  exact (restrictionVertex_self act A B₀ ψ w).symm


/-- The restriction vertex does not depend on the proof witnessing membership
in the ambient one-point closure. -/
theorem restrictionVertex_proof_irrel
    (w : WitnessVertex act A B₀ ψ)
    (y : β)
    (hy hz : y ∈ B₀.closureAtSet w.base) :
    restrictionVertex act A B₀ ψ w y hy =
      restrictionVertex act A B₀ ψ w y hz := by
  have h : hy = hz := Subsingleton.elim _ _
  subst hz
  rfl

/-- Every restriction-descendant actually belongs to the one-point closure of
the original witness vertex.  The proof is carried out inside the induced
base closure, where the centre generates the whole carrier. -/
theorem restrictionVertex_mem_closureAtSet
    (w : WitnessVertex act A B₀ ψ)
    (y : β) (hy : y ∈ B₀.closureAtSet w.base) :
    restrictionVertex act A B₀ ψ w y hy ∈
      (witnessStructure act A B₀ ψ).closureAtSet w := by
  let x0 : B₀.closureAtSet w.base :=
    ⟨w.base, B₀.mem_closureAtSet w.base⟩
  let r : B₀.closureAtSet w.base →
      WitnessVertex act A B₀ ψ :=
    fun z => restrictionVertex act A B₀ ψ w z.1 z.2
  let T : Set (B₀.closureAtSet w.base) :=
    {z | r z ∈ (witnessStructure act A B₀ ψ).closureAtSet w}
  have hTclosed : (B₀.closureAt w.base).IsClosed T := by
    intro n F zs hzs z hz
    have hconst :
        zs = fun _ => zs (UnaryFunctions.unaryIndex F) :=
      UnaryFunctions.unaryTuple_eq_constant F zs
    rw [hconst] at hz
    let u : B₀.closureAtSet w.base :=
      zs (UnaryFunctions.unaryIndex F)
    have hzB :
        z.1 ∈ B₀.func F (fun _ => u.1) := by
      change
        z.1 ∈ B₀.func F
          (Subtype.val ∘ (fun _ => u)) at hz
      simpa [Function.comp_def] using hz
    have hval :=
      functionValueVertex_restrictionVertex
        act A B₀ ψ w u.2 F hzB
    have hproof :
        r z =
          restrictionVertex act A B₀ ψ w z.1
            (B₀.closureAtSet_subset_of_mem u.2
              (func_mem_closureAtSet B₀ F hzB)) :=
      restrictionVertex_proof_irrel
        act A B₀ ψ w z.1 z.2
          (B₀.closureAtSet_subset_of_mem u.2
            (func_mem_closureAtSet B₀ F hzB))
    have hfun :
        r z ∈
          (witnessStructure act A B₀ ψ).func F
            (fun _ => r u) := by
      refine ⟨z.1, ?_, ?_⟩
      · simpa [r, u, restrictionVertex,
          WitnessVertex.base] using hzB
      · exact hproof.trans hval.symm
    have hu :
        r u ∈
          (witnessStructure act A B₀ ψ).closureAtSet w := by
      exact hzs (UnaryFunctions.unaryIndex F)
    exact
      ((witnessStructure act A B₀ ψ).isClosed_closureSet
        ({w} : Set _))
        F (fun _ => r u) (fun _ => hu) hfun
  have hx0T : x0 ∈ T := by
    change
      restrictionVertex act A B₀ ψ w w.base
          (B₀.mem_closureAtSet w.base) ∈
        (witnessStructure act A B₀ ψ).closureAtSet w
    rw [restrictionVertex_self act A B₀ ψ w]
    exact
      (witnessStructure act A B₀ ψ).mem_closureAtSet w
  have hsub :
      (B₀.closureAt w.base).closureAtSet x0 ⊆ T := by
    apply (B₀.closureAt w.base).closureSet_minimal hTclosed
    intro z hz
    have hzx : z = x0 := by simpa using hz
    subst z
    exact hx0T
  let yy : B₀.closureAtSet w.base := ⟨y, hy⟩
  have hyy :
      yy ∈ (B₀.closureAt w.base).closureAtSet x0 := by
    rw [Structure.closureAtSet_in_closureAt_eq_univ]
    exact Set.mem_univ yy
  exact hsub hyy

/-- Restriction-descendants are contained in the faithful-witness closure. -/
theorem descendants_subset_closureAtSet
    (w : WitnessVertex act A B₀ ψ) :
    {v | IsDescendant act A B₀ ψ w v} ⊆
      (witnessStructure act A B₀ ψ).closureAtSet w := by
  rintro v ⟨y, hy, rfl⟩
  exact restrictionVertex_mem_closureAtSet act A B₀ ψ w y hy

/-- **Closure characterization.**  One-point closure in the faithful witness
is exactly restriction of the valuation structure along the corresponding
base one-point closure. -/
theorem closureAtSet_eq_descendants
    (w : WitnessVertex act A B₀ ψ) :
    (witnessStructure act A B₀ ψ).closureAtSet w =
      {v | IsDescendant act A B₀ ψ w v} := by
  apply Set.Subset.antisymm
  · exact closureAtSet_subset_descendants act A B₀ ψ w
  · exact descendants_subset_closureAtSet act A B₀ ψ w


/-- Any unary function value belongs to the one-point closure of its input in
the faithful witness itself. -/
theorem witness_func_mem_closureAtSet
    {x y : WitnessVertex act A B₀ ψ}
    {n : ℕ} (F : L.FuncSymbol n)
    (hy :
      y ∈
        (witnessStructure act A B₀ ψ).func F (fun _ => x)) :
    y ∈ (witnessStructure act A B₀ ψ).closureAtSet x := by
  change
    y ∈ (witnessStructure act A B₀ ψ).closureSet {x}
  exact
    ((witnessStructure act A B₀ ψ).isClosed_closureSet
      ({x} : Set _))
      F (fun _ => x)
      (fun _ => (witnessStructure act A B₀ ψ).mem_closureAtSet x)
      hy

/-- Looking at an internal valuation point after restriction is literally the
same as looking at the corresponding point of the original valuation
structure. -/
theorem restrictionVertex_pointAt
    (w : WitnessVertex act A B₀ ψ)
    {y : β} (hy : y ∈ B₀.closureAtSet w.base)
    (z : B₀.closureAtSet y) :
    (restrictionVertex act A B₀ ψ w y hy).pointAt
        act A B₀ ψ z =
      w.pointAt act A B₀ ψ
        (closureInclusion B₀ hy z) :=
  rfl

/-- Every valuation point of a vertex in the closure of `w` is represented
by an internal valuation point of `w`. -/
theorem pointAt_eq_ancestor_of_mem_closure
    (w x : WitnessVertex act A B₀ ψ)
    (hx :
      x ∈ (witnessStructure act A B₀ ψ).closureAtSet w)
    (u : B₀.closureAtSet x.base) :
    ∃ u' : B₀.closureAtSet w.base,
      x.pointAt act A B₀ ψ u =
        w.pointAt act A B₀ ψ u' := by
  rw [closureAtSet_eq_descendants act A B₀ ψ w] at hx
  rcases hx with ⟨y, hy, rfl⟩
  exact
    ⟨closureInclusion B₀ hy u,
      restrictionVertex_pointAt act A B₀ ψ w hy u⟩

/-- Two descendants of the same witness vertex have pairwise generic internal
valuation points. -/
theorem points_generic_of_mem_closure_same_ancestor
    (w x y : WitnessVertex act A B₀ ψ)
    (hx :
      x ∈ (witnessStructure act A B₀ ψ).closureAtSet w)
    (hy :
      y ∈ (witnessStructure act A B₀ ψ).closureAtSet w)
    (u : B₀.closureAtSet x.base)
    (v : B₀.closureAtSet y.base) :
    AreGeneric act A B₀ ψ
      (x.pointAt act A B₀ ψ u)
      (y.pointAt act A B₀ ψ v) := by
  rcases
      pointAt_eq_ancestor_of_mem_closure
        act A B₀ ψ w x hx u with
    ⟨u', hu⟩
  rcases
      pointAt_eq_ancestor_of_mem_closure
        act A B₀ ψ w y hy v with
    ⟨v', hv⟩
  rw [hu, hv]
  exact w.valuation.2 u' v'

end Faithful
end AllThoseEPPA
