import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Basic
import AllThoseEPPA.InfiniteRelational

/-!
# EPPA for structures with unary functions

This file formalizes Proposition `prop:eppafunctions` of the paper.

The paper packages a valuation at a base point as a small structure `V`
whose relational reduct sits inside a relational EPPA witness and which is
isomorphic, up to language relabelling, to a one-point closure in `A`.

For Lean we use an equivalent finite code: an element of the finite
relabelling orbit of `A`, a centre in that orbit structure, and an
identity-language embedding of its one-point relational closure into the
relational witness.  This absorbs the choice of a group element into the
finite orbit and avoids carrying infinitely many duplicate valuation codes.
-/

namespace AllThoseEPPA
namespace UnaryFunctions

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v} [Fintype α]
variable (act : L.Action Γ) (A : Structure L α)

/-- The relabelling orbit of a structure, with the structure itself retained
as data.  Under the finite-orbit hypothesis this is a finite type. -/
abbrev Orbit :=
  {B : Structure L α // B ∈ Set.range fun g : Γ => A.relabel act g}

noncomputable def orbitFintype
    (hA : A.HasFiniteRelabelOrbit act) :
    Fintype (Orbit act A) :=
  Set.Finite.fintype hA

/-- Relabel one member of the orbit. -/
def orbitRelabel (g : Γ) : Orbit act A ≃ Orbit act A where
  toFun := fun B => by
    refine ⟨B.1.relabel act g, ?_⟩
    rcases B.2 with ⟨h, hB⟩
    refine ⟨g * h, ?_⟩
    calc
      A.relabel act (g * h) = (A.relabel act h).relabel act g :=
        (Structure.relabel_mul act g h A).symm
      _ = B.1.relabel act g :=
        congrArg (fun C => C.relabel act g) hB
  invFun := fun B => by
    refine ⟨B.1.relabel act g⁻¹, ?_⟩
    rcases B.2 with ⟨h, hB⟩
    refine ⟨g⁻¹ * h, ?_⟩
    calc
      A.relabel act (g⁻¹ * h) = (A.relabel act h).relabel act g⁻¹ :=
        (Structure.relabel_mul act g⁻¹ h A).symm
      _ = B.1.relabel act g⁻¹ :=
        congrArg (fun C => C.relabel act g⁻¹) hB
  left_inv := by
    intro B
    apply Subtype.ext
    change (B.1.relabel act g).relabel act g⁻¹ = B.1
    rw [Structure.relabel_mul]
    simp
  right_inv := by
    intro B
    apply Subtype.ext
    change (B.1.relabel act g⁻¹).relabel act g = B.1
    rw [Structure.relabel_mul]
    simp

@[simp] theorem orbitRelabel_val (g : Γ) (B : Orbit act A) :
    (orbitRelabel act A g B).1 = B.1.relabel act g :=
  rfl

/-- Relabelling does not change which subsets are closed: it only permutes the
function-symbol names. -/
theorem isClosed_relabel_iff
    (g : Γ) (B : Structure L α) (S : Set α) :
    (B.relabel act g).IsClosed S ↔ B.IsClosed S := by
  constructor
  · intro h
    intro n F xs hxs y hy
    have hy' :
        y ∈ (B.relabel act g).func (act.onFunc g F) xs := by
      simpa [Structure.relabel_func, ← Language.Action.onFunc_mul] using hy
    exact h (act.onFunc g F) xs hxs hy'
  · intro h
    intro n F xs hxs y hy
    have hsub := h (act.onFunc g⁻¹ F) xs hxs
    exact hsub (by simpa [Structure.relabel_func] using hy)

/-- Consequently, one-point closure sets are invariant under relabelling. -/
theorem closureAtSet_relabel
    (g : Γ) (B : Structure L α) (x : α) :
    (B.relabel act g).closureAtSet x = B.closureAtSet x := by
  apply Set.Subset.antisymm
  · apply (B.relabel act g).closureSet_minimal
    · exact (isClosed_relabel_iff act g B (B.closureAtSet x)).2
        (B.isClosed_closureSet {x})
    · intro y hy
      have hxy : y = x := by simpa using hy
      subst y
      exact B.mem_closureAtSet x
  · apply B.closureSet_minimal
    · exact (isClosed_relabel_iff act g B
        ((B.relabel act g).closureAtSet x)).1
        ((B.relabel act g).isClosed_closureSet {x})
    · intro y hy
      have hxy : y = x := by simpa using hy
      subst y
      exact (B.relabel act g).mem_closureAtSet x

/-- Forgetting the function symbols of a partial automorphism leaves the same
language component and the same underlying partial equivalence. -/
def reductPartialAutomorphism
    (p : Structure.PartialAutomorphism act A) :
    Structure.PartialAutomorphism act.relationalReduct
      A.relationalReduct where
  lang := p.lang
  toPartialEquiv := p.toPartialEquiv
  source_closed := by
    intro n F xs hxs
    exact PEmpty.elim F
  target_closed := by
    intro n F xs hxs
    exact PEmpty.elim F
  map_rel_iff := by
    intro n R xs hxs
    exact p.map_rel_iff R xs hxs
  map_func := by
    intro n F xs hxs
    exact PEmpty.elim F

@[simp] theorem reductPartialAutomorphism_lang
    (p : Structure.PartialAutomorphism act A) :
    (reductPartialAutomorphism act A p).lang = p.lang :=
  rfl

@[simp] theorem reductPartialAutomorphism_partialEquiv
    (p : Structure.PartialAutomorphism act A) :
    (reductPartialAutomorphism act A p).toPartialEquiv =
      p.toPartialEquiv :=
  rfl

theorem reductPartialAutomorphism_equivalent
    {p q : Structure.PartialAutomorphism act A}
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    Structure.PartialIsomorphism.Equivalent
      (reductPartialAutomorphism act A p)
      (reductPartialAutomorphism act A q) :=
  hpq

theorem reductPartialAutomorphism_coherentTriple
    {p q r : Structure.PartialAutomorphism act A}
    (h : Structure.PartialIsomorphism.CoherentTriple p q r) :
    Structure.PartialIsomorphism.CoherentTriple
      (reductPartialAutomorphism act A p)
      (reductPartialAutomorphism act A q)
      (reductPartialAutomorphism act A r) := by
  rcases h with ⟨htg, hr⟩
  exact ⟨htg, hr⟩

end UnaryFunctions
end AllThoseEPPA
