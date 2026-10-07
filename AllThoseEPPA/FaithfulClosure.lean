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
  apply congrArg V.1
  apply Subtype.ext
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
  apply congrArg V.1
  apply Subtype.ext
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
  have hconst :
      xs = fun _ => xs (UnaryFunctions.unaryIndex F) :=
    UnaryFunctions.unaryTuple_eq_constant F xs
  rcases hxs (UnaryFunctions.unaryIndex F) with
    ⟨y, hy, hxy⟩
  rw [hconst] at hz
  rcases hz with ⟨t, ht, hzt⟩
  subst z
  rw [hxy] at ht ⊢
  have ht' :
      t ∈ B₀.func F (fun _ => y) := by
    simpa [restrictionVertex, WitnessVertex.base] using ht
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
  let C := B₀.closureAt w.base
  let x0 : C := ⟨w.base, B₀.mem_closureAtSet w.base⟩
  let r : C → WitnessVertex act A B₀ ψ :=
    fun z => restrictionVertex act A B₀ ψ w z.1 z.2
  let T : Set C :=
    {z | r z ∈ (witnessStructure act A B₀ ψ).closureAtSet w}
  have hTclosed : C.IsClosed T := by
    intro n F zs hzs z hz
    have hconst :
        zs = fun _ => zs (UnaryFunctions.unaryIndex F) :=
      UnaryFunctions.unaryTuple_eq_constant F zs
    rw [hconst] at hz
    let u : C := zs (UnaryFunctions.unaryIndex F)
    have hzB :
        z.1 ∈ B₀.func F (fun _ => u.1) := by
      simpa [C, u, Function.comp_def] using hz
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
      · simpa [r, u, restrictionVertex, WitnessVertex.base] using hzB
      · exact hproof.trans hval.symm
    have hu :
        r u ∈
          (witnessStructure act A B₀ ψ).closureAtSet w := by
      exact hzs (UnaryFunctions.unaryIndex F)
    exact
      ((witnessStructure act A B₀ ψ).isClosed_closureSet ({w} : Set _))
        F (fun _ => r u) (fun _ => hu) hfun
  have hx0T : x0 ∈ T := by
    change
      restrictionVertex act A B₀ ψ w w.base
          (B₀.mem_closureAtSet w.base) ∈
        (witnessStructure act A B₀ ψ).closureAtSet w
    rw [restrictionVertex_self act A B₀ ψ w]
    exact
      (witnessStructure act A B₀ ψ).mem_closureAtSet w
  have hsub : C.closureAtSet x0 ⊆ T := by
    apply C.closureSet_minimal hTclosed
    intro z hz
    have hzx : z = x0 := by simpa using hz
    subst z
    exact hx0T
  let yy : C := ⟨y, hy⟩
  have hyy : yy ∈ C.closureAtSet x0 := by
    rw [Structure.closureAtSet_in_closureAt_eq_univ]
    exact Set.mem_univ yy
  have hout := hsub hyy
  exact hout

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

end Faithful
end AllThoseEPPA
