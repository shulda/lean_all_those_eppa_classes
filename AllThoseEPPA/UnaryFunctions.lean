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
    (embedding act A B₀ v) y = v.toFun y :=
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
    have h' :
        (⟨z.1, v.orbit.1.closureAtSet_subset_of_mem hy z.2⟩ :
            v.orbit.1.closureAtSet v.center) =
          ⟨z'.1, v.orbit.1.closureAtSet_subset_of_mem hy z'.2⟩ :=
      v.injective h
    apply Subtype.ext
    exact congrArg
      (fun t : v.orbit.1.closureAtSet v.center => t.1) h'
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
    (z : (restrict act A B₀ v y hy).orbit.1.closureAtSet
      (restrict act A B₀ v y hy).center) :
    (restrict act A B₀ v y hy).toFun z =
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
  letI : Fintype β := Fintype.ofFinite β
  letI (C : Orbit act A) (y : α) :
      Fintype (C.1.closureAtSet y) :=
    Fintype.ofFinite _
  haveI : Finite (Code act A (β := β)) := by
    infer_instance
  exact Finite.of_injective
    (code act A B₀ (x := x))
    (code_injective act A B₀ (x := x))

end Valuation
end Valuations


section Witness

variable {β : Type z} [Finite β]
variable (B₀ : Structure L.relationalReduct β)

/-- The unique input coordinate of a function symbol. -/
def unaryIndex {n : ℕ} (F : L.FuncSymbol n) : Fin n := by
  have hn : n = 1 := Language.HasUnaryFunctions.arity_eq_one F
  subst n
  exact 0

/-- A tuple for a unary function has only one relevant entry. -/
theorem unaryTuple_eq_constant {X : Type*} {n : ℕ}
    (F : L.FuncSymbol n) (xs : Fin n → X) :
    xs = fun _ => xs (unaryIndex F) := by
  funext i
  have hn : n = 1 := Language.HasUnaryFunctions.arity_eq_one F
  subst n
  exact Fin.eq_zero i ▸ rfl

/-- Vertices of the unary-function witness are the paper's pairs `(x,V)`. -/
abbrev WitnessVertex :=
  Σ x : β, Valuation act A B₀ x

/-- Projection of a witness vertex to the relational base witness. -/
def WitnessVertex.base (w : WitnessVertex act A B₀) : β :=
  w.1

/-- The valuation carried by a witness vertex. -/
def WitnessVertex.valuation (w : WitnessVertex act A B₀) :
    Valuation act A B₀ w.base :=
  w.2

/-- The centre of the orbit closure represented by a witness valuation. -/
def WitnessVertex.center (w : WitnessVertex act A B₀) : α :=
  w.2.center

/-- Every function value of the centre lies in its one-point closure. -/
theorem Valuation.func_mem_closure {x : β}
    (v : Valuation act A B₀ x)
    {n : ℕ} (F : L.FuncSymbol n)
    {y : α}
    (hy : y ∈ v.orbit.1.func F (fun _ => v.center)) :
    y ∈ v.orbit.1.closureAtSet v.center := by
  change y ∈ v.orbit.1.closureSet {v.center}
  exact
    (v.orbit.1.isClosed_closureSet ({v.center} : Set α))
      F (fun _ => v.center)
      (fun _ => v.orbit.1.mem_closureAtSet v.center) hy

/-- The witness vertex obtained from a value `y ∈ F_V(x)`: retain the image
of `y` in the relational base and restrict the valuation to `cl_V(y)`. -/
def functionValueVertex {x : β}
    (v : Valuation act A B₀ x)
    {n : ℕ} (F : L.FuncSymbol n)
    (y : α) (hy : y ∈ v.orbit.1.func F (fun _ => v.center)) :
    WitnessVertex act A B₀ :=
  let hycl := Valuation.func_mem_closure act A B₀ v F hy
  ⟨v.toFun ⟨y, hycl⟩,
    Valuation.restrict act A B₀ v y hycl⟩

@[simp] theorem functionValueVertex_base {x : β}
    (v : Valuation act A B₀ x)
    {n : ℕ} (F : L.FuncSymbol n)
    (y : α) (hy : y ∈ v.orbit.1.func F (fun _ => v.center)) :
    (functionValueVertex act A B₀ v F y hy).base =
      v.toFun
        ⟨y, Valuation.func_mem_closure act A B₀ v F hy⟩ :=
  rfl

/-- The structure `B` from Proposition `prop:eppafunctions`.

Relations are pulled back from `B₀` along the base projection.  A unary
function follows the local valuation structure and replaces it by the
one-point closure at the chosen function value. -/
def witnessStructure : Structure L (WitnessVertex act A B₀) where
  rel := by
    intro n R ws
    exact B₀.rel R (fun i => (ws i).base)
  func := by
    intro n F ws
    let w := ws (unaryIndex F)
    exact
      {z | ∃ (y : α)
        (hy : y ∈ w.valuation.orbit.1.func F
          (fun _ => w.valuation.center)),
        z = functionValueVertex act A B₀ w.valuation F y hy}

/-- Relation membership in the witness only sees the base projection. -/
@[simp] theorem witnessStructure_rel_iff
    {n : ℕ} (R : L.RelSymbol n)
    (ws : Fin n → WitnessVertex act A B₀) :
    (witnessStructure act A B₀).rel R ws ↔
      B₀.rel R (fun i => (ws i).base) :=
  Iff.rfl

/-- A convenient membership form for function values in the witness. -/
theorem mem_witnessStructure_func_iff
    {n : ℕ} (F : L.FuncSymbol n)
    (ws : Fin n → WitnessVertex act A B₀)
    (z : WitnessVertex act A B₀) :
    z ∈ (witnessStructure act A B₀).func F ws ↔
      ∃ (y : α)
        (hy : y ∈
          (ws (unaryIndex F)).valuation.orbit.1.func F
            (fun _ => (ws (unaryIndex F)).valuation.center)),
        z =
          functionValueVertex act A B₀
            (ws (unaryIndex F)).valuation F y hy := by
  rfl

/-- The unary-function witness is finite whenever the relabelling orbit of
`A` is finite and the relational base witness is finite. -/
theorem witnessVertex_finite
    (hA : A.HasFiniteRelabelOrbit act) :
    Finite (WitnessVertex act A B₀) := by
  letI : Fintype β := Fintype.ofFinite β
  letI (x : β) : Finite (Valuation act A B₀ x) :=
    Valuation.finite act A B₀ hA x
  letI (x : β) : Fintype (Valuation act A B₀ x) :=
    Fintype.ofFinite _
  exact Fintype.finite _

end Witness

end UnaryFunctions
end AllThoseEPPA
