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


section Valuations

variable {β : Type z} [Finite β]
variable (B₀ : Structure L.relationalReduct β)

/-- A finite code for the paper's valuation structure at a base point `x`.

The orbit member absorbs the language part of the isomorphism to a one-point
closure.  The map `toFun` embeds that relational closure into `B₀` with
the identity language permutation, and sends its centre to `x`. -/
structure Valuation (x : β) where
  orbit : Orbit act A
  center : α
  toFun : orbit.1.closureAtSet center → β
  injective : Function.Injective toFun
  map_rel_iff :
    ∀ {n : ℕ} (R : L.RelSymbol n)
      (xs : Fin n → orbit.1.closureAtSet center),
      B₀.rel R (toFun ∘ xs) ↔
        orbit.1.rel R (Subtype.val ∘ xs)
  center_eq :
    toFun ⟨center, orbit.1.mem_closureAtSet center⟩ = x

namespace Valuation

/-- A valuation code determines a genuine embedding of the relational
one-point closure into the base relational witness. -/
def embedding {x : β} (v : Valuation act A B₀ x) :
    Structure.Embedding act.relationalReduct
      (v.orbit.1.closureAt v.center).relationalReduct B₀ where
  lang := 1
  toFun := v.toFun
  injective := v.injective
  map_rel_iff := by
    intro n R xs
    rw [Language.Action.onRel_one]
    exact v.map_rel_iff R xs
  map_func := by
    intro n F xs
    exact PEmpty.elim F

@[simp] theorem embedding_apply {x : β}
    (v : Valuation act A B₀ x)
    (y : v.orbit.1.closureAtSet v.center) :
    v.embedding y = v.toFun y :=
  rfl

/-- Restrict a valuation from the closure of its centre to the closure of a
point lying inside it.  This is the formal counterpart of
`cl_V(y)` in the paper. -/
def restrict {x : β} (v : Valuation act A B₀ x)
    (y : α) (hy : y ∈ v.orbit.1.closureAtSet v.center) :
    Valuation act A B₀ (v.toFun ⟨y, hy⟩) where
  orbit := v.orbit
  center := y
  toFun := fun z =>
    v.toFun
      ⟨z.1, v.orbit.1.closureAtSet_subset_of_mem hy z.2⟩
  injective := by
    intro z z' h
    apply Subtype.ext
    apply v.injective at h
    exact congrArg Subtype.val h
  map_rel_iff := by
    intro n R xs
    let ys : Fin n → v.orbit.1.closureAtSet v.center :=
      fun i =>
        ⟨(xs i).1,
          v.orbit.1.closureAtSet_subset_of_mem hy (xs i).2⟩
    have h := v.map_rel_iff R ys
    simpa [ys, Function.comp_def] using h
  center_eq := rfl

@[simp] theorem restrict_toFun {x : β}
    (v : Valuation act A B₀ x)
    (y : α) (hy : y ∈ v.orbit.1.closureAtSet v.center)
    (z : (v.restrict y hy).orbit.1.closureAtSet
      (v.restrict y hy).center) :
    (v.restrict y hy).toFun z =
      v.toFun
        ⟨z.1, v.orbit.1.closureAtSet_subset_of_mem hy z.2⟩ :=
  rfl

/-- The finite data underlying a valuation, with all proof fields erased. -/
abbrev Code :=
  Σ C : Orbit act A, Σ y : α, C.1.closureAtSet y → β

def code {x : β} (v : Valuation act A B₀ x) :
    Code act A (β := β) :=
  ⟨v.orbit, v.center, v.toFun⟩

theorem code_injective {x : β} :
    Function.Injective (code act A B₀ (x := x)) := by
  intro v w h
  cases v with
  | mk Cv yv fv hiv hrv hcv =>
    cases w with
    | mk Cw yw fw hiw hrw hcw =>
      change (⟨Cv, yv, fv⟩ : Code act A (β := β)) =
        ⟨Cw, yw, fw⟩ at h
      cases h
      rfl

/-- There are only finitely many valuation structures over a fixed base point.
This is the finiteness argument from Proposition `prop:eppafunctions`, with
the finite relabelling orbit used directly as part of the code. -/
theorem finite
    (hA : A.HasFiniteRelabelOrbit act) (x : β) :
    Finite (Valuation act A B₀ x) := by
  classical
  letI : Fintype (Orbit act A) := orbitFintype act A hA
  apply Finite.of_injective
    (code act A B₀ (x := x))
    (code_injective act A B₀ (x := x))

end Valuation
end Valuations

end UnaryFunctions
end AllThoseEPPA
