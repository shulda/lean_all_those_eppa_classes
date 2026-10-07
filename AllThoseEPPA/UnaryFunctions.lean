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


@[simp] theorem unaryIndex_onFunc
    (g : Γ) {n : ℕ} (F : L.FuncSymbol n) :
    unaryIndex (act.onFunc g F) = unaryIndex F :=
  Subsingleton.elim _ _

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
  classical
  letI : Fintype β := Fintype.ofFinite β
  letI : Fintype (Orbit act A) := orbitFintype act A hA
  letI (C : Orbit act A) (y : α) :
      Fintype (C.1.closureAtSet y) :=
    Fintype.ofFinite _
  haveI : Finite (Valuation.Code act A (β := β)) := by
    infer_instance
  let code :
      WitnessVertex act A B₀ →
        β × Valuation.Code act A (β := β) :=
    fun w => (w.1, Valuation.code act A B₀ w.2)
  apply Finite.of_injective code
  rintro ⟨x, v⟩ ⟨y, w⟩ h
  have hxy : x = y := congrArg Prod.fst h
  subst y
  have hv :
      Valuation.code act A B₀ v =
        Valuation.code act A B₀ w :=
    congrArg Prod.snd h
  have hvw : v = w :=
    Valuation.code_injective act A B₀ hv
  subst w
  rfl

end Witness


section PhysicalValuations

variable {β : Type z} [Finite β]
variable (B₀ : Structure L.relationalReduct β)

/-- The physical information in a valuation structure after its abstract
closure coordinates have been embedded into the relational base witness.

Relations need not be stored: on the support they are forced by `B₀`.
For unary functions we record, for every supported base vertex, the physical
set of function values in `β`.  This deliberately forgets the auxiliary
orbit/coordinate presentation used only to prove finiteness. -/
@[ext] structure ValuationSignature (x : β) where
  support : Set β
  center_mem : x ∈ support
  func : {n : ℕ} → L.FuncSymbol n → β → Set β
  func_supported :
    ∀ {n : ℕ} (F : L.FuncSymbol n) {a : β},
      a ∈ support → func F a ⊆ support

/-- A function value at an arbitrary point of an abstract valuation closure
still lies in that closure. -/
theorem Valuation.func_mem_closure_of_mem {x : β}
    (v : Valuation act A B₀ x)
    (a : v.orbit.1.closureAtSet v.center)
    {n : ℕ} (F : L.FuncSymbol n)
    {y : α}
    (hy : y ∈ v.orbit.1.func F (fun _ => a.1)) :
    y ∈ v.orbit.1.closureAtSet v.center := by
  change y ∈ v.orbit.1.closureSet {v.center}
  exact
    (v.orbit.1.isClosed_closureSet ({v.center} : Set α))
      F (fun _ => a.1) (fun _ => a.2) hy

/-- The physical `F`-values represented by an abstract valuation code at a
base vertex `a ∈ β`.  The existential presentation makes the definition
independent of choosing an inverse to the embedding `v.toFun`. -/
def Valuation.physicalFunc {x : β}
    (v : Valuation act A B₀ x)
    {n : ℕ} (F : L.FuncSymbol n) (a : β) : Set β :=
  {b | ∃ (z : v.orbit.1.closureAtSet v.center),
      v.toFun z = a ∧
        ∃ (y : α)
          (hy : y ∈ v.orbit.1.func F (fun _ => z.1)),
          b =
            v.toFun
              ⟨y, Valuation.func_mem_closure_of_mem
                act A B₀ v z F hy⟩}

/-- Forget the abstract orbit coordinates of a valuation code, retaining only
the actual support and unary-function structure carried inside `B₀`. -/
def Valuation.physicalSignature {x : β}
    (v : Valuation act A B₀ x) :
    ValuationSignature (L := L) x where
  support := Set.range v.toFun
  center_mem := by
    refine ⟨⟨v.center, v.orbit.1.mem_closureAtSet v.center⟩, ?_⟩
    exact v.center_eq
  func := fun F a => Valuation.physicalFunc act A B₀ v F a
  func_supported := by
    intro n F a ha b hb
    rcases hb with ⟨z, hza, y, hy, hby⟩
    refine ⟨
      ⟨y, Valuation.func_mem_closure_of_mem act A B₀ v z F hy⟩,
      ?_⟩
    exact hby.symm

/-- A physical valuation is a signature realised by at least one finite
abstract valuation code.  Presentation choices are therefore quotiented out
by ordinary equality of their physical signatures. -/
abbrev PhysicalValuation (x : β) :=
  {s : ValuationSignature (L := L) x //
    s ∈ Set.range (Valuation.physicalSignature act A B₀)}

/-- Every physical valuation has a finite presentation set, because it is the
range of the already finite abstract valuation-code type. -/
noncomputable def physicalValuationFintype
    (hA : A.HasFiniteRelabelOrbit act) (x : β) :
    Fintype (PhysicalValuation act A B₀ x) := by
  letI : Finite (Valuation act A B₀ x) :=
    Valuation.finite act A B₀ hA x
  exact Set.Finite.fintype (Set.finite_range _)

/-- In particular, the physical valuation fibre over each base point is
finite. -/
theorem physicalValuation_finite
    (hA : A.HasFiniteRelabelOrbit act) (x : β) :
    Finite (PhysicalValuation act A B₀ x) := by
  letI : Fintype (PhysicalValuation act A B₀ x) :=
    physicalValuationFintype act A B₀ hA x
  infer_instance

namespace ValuationSignature

/-- Closed subsets for the unary-function data carried by a physical
valuation signature. -/
def IsClosed {x : β}
    (s : ValuationSignature (L := L) x) (T : Set β) : Prop :=
  ∀ {n : ℕ} (F : L.FuncSymbol n) {a : β},
    a ∈ T → s.func F a ⊆ T

/-- The support of a physical valuation is closed under all its unary
functions. -/
theorem support_closed {x : β}
    (s : ValuationSignature (L := L) x) :
    s.IsClosed s.support := by
  intro n F a ha
  exact s.func_supported F ha

/-- Closure generated by a set inside a physical valuation signature. -/
def closureSet {x : β}
    (s : ValuationSignature (L := L) x) (S : Set β) : Set β :=
  {a | ∀ T : Set β, s.IsClosed T → S ⊆ T → a ∈ T}

/-- Every set lies in its signature closure. -/
theorem subset_closureSet {x : β}
    (s : ValuationSignature (L := L) x) (S : Set β) :
    S ⊆ s.closureSet S := by
  intro a ha T hT hST
  exact hST ha

/-- Signature closure is closed. -/
theorem isClosed_closureSet {x : β}
    (s : ValuationSignature (L := L) x) (S : Set β) :
    s.IsClosed (s.closureSet S) := by
  intro n F a ha b hb T hT hST
  apply hT F
  · exact ha T hT hST
  · exact hb

/-- Signature closure is the least closed superset. -/
theorem closureSet_minimal {x : β}
    (s : ValuationSignature (L := L) x)
    {S T : Set β} (hT : s.IsClosed T) (hST : S ⊆ T) :
    s.closureSet S ⊆ T := by
  intro a ha
  exact ha T hT hST

/-- One-point closure inside a physical valuation signature. -/
def closureAtSet {x : β}
    (s : ValuationSignature (L := L) x) (y : β) : Set β :=
  s.closureSet {y}

/-- The generating point belongs to its one-point closure. -/
theorem mem_closureAtSet {x : β}
    (s : ValuationSignature (L := L) x) (y : β) :
    y ∈ s.closureAtSet y := by
  exact s.subset_closureSet {y} (by simp)

/-- If the new centre belongs to the old support, its generated closure stays
inside that support. -/
theorem closureAtSet_subset_support {x : β}
    (s : ValuationSignature (L := L) x)
    {y : β} (hy : y ∈ s.support) :
    s.closureAtSet y ⊆ s.support := by
  apply s.closureSet_minimal s.support_closed
  intro z hz
  have hzy : z = y := by simpa using hz
  subst z
  exact hy

/-- Restrict a physical valuation signature to the one-point closure of a
supported vertex.  Outside the smaller support all function values are
masked to the empty set; on the support they are unchanged. -/
noncomputable def restrict {x : β}
    (s : ValuationSignature (L := L) x)
    (y : β) (hy : y ∈ s.support) :
    ValuationSignature (L := L) y := by
  classical
  refine
    { support := s.closureAtSet y
      center_mem := s.mem_closureAtSet y
      func := fun F a =>
        if ha : a ∈ s.closureAtSet y then s.func F a else ∅
      func_supported := ?_ }
  intro n F a ha b hb
  simp [ha] at hb
  exact (s.isClosed_closureSet {y}) F ha hb

@[simp] theorem restrict_support {x : β}
    (s : ValuationSignature (L := L) x)
    (y : β) (hy : y ∈ s.support) :
    (s.restrict y hy).support = s.closureAtSet y :=
  rfl

@[simp] theorem restrict_func_of_mem {x : β}
    (s : ValuationSignature (L := L) x)
    (y : β) (hy : y ∈ s.support)
    {n : ℕ} (F : L.FuncSymbol n) {a : β}
    (ha : a ∈ s.closureAtSet y) :
    (s.restrict y hy).func F a = s.func F a := by
  simp [restrict, ha]

@[simp] theorem restrict_func_of_not_mem {x : β}
    (s : ValuationSignature (L := L) x)
    (y : β) (hy : y ∈ s.support)
    {n : ℕ} (F : L.FuncSymbol n) {a : β}
    (ha : a ∉ s.closureAtSet y) :
    (s.restrict y hy).func F a = ∅ := by
  simp [restrict, ha]

end ValuationSignature

/-- At a point in the embedded abstract closure, the physical function values
are exactly the images of the corresponding abstract function values. -/
theorem Valuation.mem_physicalFunc_at_image_iff
    {x : β} (v : Valuation act A B₀ x)
    (z : v.orbit.1.closureAtSet v.center)
    {n : ℕ} (F : L.FuncSymbol n) (b : β) :
    b ∈ Valuation.physicalFunc act A B₀ v F (v.toFun z) ↔
      ∃ (y : α)
        (hy : y ∈ v.orbit.1.func F (fun _ => z.1)),
        b =
          v.toFun
            ⟨y, Valuation.func_mem_closure_of_mem
              act A B₀ v z F hy⟩ := by
  constructor
  · rintro ⟨z', hz', y, hy, hby⟩
    have hzz : z' = z := v.injective hz'
    subst z'
    exact ⟨y, hy, hby⟩
  · rintro ⟨y, hy, hby⟩
    exact ⟨z, rfl, y, hy, hby⟩

/-- The physical image of the one-point closure generated by `y` inside an
abstract valuation presentation. -/
def Valuation.imageClosure
    {x : β} (v : Valuation act A B₀ x)
    (y : α) (hy : y ∈ v.orbit.1.closureAtSet v.center) :
    Set β :=
  {b | ∃ z : v.orbit.1.closureAtSet y,
      b =
        v.toFun
          ⟨z.1, v.orbit.1.closureAtSet_subset_of_mem hy z.2⟩}

/-- The image of a smaller abstract one-point closure is closed for the
physical unary-function data. -/
theorem Valuation.imageClosure_isClosed
    {x : β} (v : Valuation act A B₀ x)
    (y : α) (hy : y ∈ v.orbit.1.closureAtSet v.center) :
    (Valuation.physicalSignature act A B₀ v).IsClosed
      (Valuation.imageClosure act A B₀ v y hy) := by
  intro n F a ha b hb
  rcases ha with ⟨z, rfl⟩
  let z₀ : v.orbit.1.closureAtSet v.center :=
    ⟨z.1, v.orbit.1.closureAtSet_subset_of_mem hy z.2⟩
  have hb' :
      b ∈ Valuation.physicalFunc act A B₀ v F (v.toFun z₀) :=
    hb
  rcases
      (Valuation.mem_physicalFunc_at_image_iff
        act A B₀ v z₀ F b).1 hb' with
    ⟨t, ht, hbt⟩
  have htcl : t ∈ v.orbit.1.closureAtSet y := by
    change t ∈ v.orbit.1.closureSet {y}
    exact
      (v.orbit.1.isClosed_closureSet ({y} : Set α))
        F (fun _ => z.1) (fun _ => z.2) ht
  refine ⟨⟨t, htcl⟩, ?_⟩
  rw [hbt]


/-- One-point closure in the physical signature is exactly the embedded image
of the corresponding abstract one-point closure. -/
theorem Valuation.physicalSignature_closureAt_image
    {x : β} (v : Valuation act A B₀ x)
    (y : α) (hy : y ∈ v.orbit.1.closureAtSet v.center) :
    (Valuation.physicalSignature act A B₀ v).closureAtSet
        (v.toFun ⟨y, hy⟩) =
      Valuation.imageClosure act A B₀ v y hy := by
  let s := Valuation.physicalSignature act A B₀ v
  let y₀ : v.orbit.1.closureAtSet v.center := ⟨y, hy⟩
  apply Set.Subset.antisymm
  · apply
      (s.closureSet_minimal
        (Valuation.imageClosure_isClosed act A B₀ v y hy))
    intro b hb
    have hby : b = v.toFun y₀ := by
      simpa [y₀] using hb
    subst b
    refine
      ⟨⟨y, v.orbit.1.mem_closureAtSet y⟩, ?_⟩
    apply congrArg v.toFun
    apply Subtype.ext
    rfl
  · rintro b ⟨z, rfl⟩
    let T : Set α :=
      {a | ∃ ha : a ∈ v.orbit.1.closureAtSet v.center,
          v.toFun ⟨a, ha⟩ ∈ s.closureAtSet (v.toFun y₀)}
    have hTclosed : v.orbit.1.IsClosed T := by
      intro n F xs hxs t ht
      rcases hxs (unaryIndex F) with ⟨ha, himg⟩
      have htuple := unaryTuple_eq_constant F xs
      rw [htuple] at ht
      have htcenter : t ∈ v.orbit.1.closureAtSet v.center := by
        change t ∈ v.orbit.1.closureSet {v.center}
        exact
          (v.orbit.1.isClosed_closureSet ({v.center} : Set α))
            F (fun _ => xs (unaryIndex F)) (fun _ => ha) ht
      have hphys :
          v.toFun ⟨t, htcenter⟩ ∈
            s.func F (v.toFun ⟨xs (unaryIndex F), ha⟩) := by
        change
          v.toFun ⟨t, htcenter⟩ ∈
            Valuation.physicalFunc act A B₀ v F
              (v.toFun ⟨xs (unaryIndex F), ha⟩)
        apply
          (Valuation.mem_physicalFunc_at_image_iff
            act A B₀ v ⟨xs (unaryIndex F), ha⟩ F
              (v.toFun ⟨t, htcenter⟩)).2
        refine ⟨t, ht, ?_⟩
        apply congrArg v.toFun
        apply Subtype.ext
        rfl
      have hout :
          v.toFun ⟨t, htcenter⟩ ∈
            s.closureAtSet (v.toFun y₀) :=
        (s.isClosed_closureSet {v.toFun y₀}) F himg hphys
      exact ⟨htcenter, hout⟩
    have hyT : y ∈ T := by
      refine ⟨hy, ?_⟩
      exact s.mem_closureAtSet (v.toFun y₀)
    have hzT : z.1 ∈ T := by
      have hsub : ({y} : Set α) ⊆ T := by
        intro a ha
        have hay : a = y := by
          simpa using ha
        subst a
        exact hyT
      exact
        (v.orbit.1.closureSet_minimal hTclosed hsub) z.2
    rcases hzT with ⟨hzcenter, hzimage⟩
    have hzsub :
        (⟨z.1, hzcenter⟩ :
          v.orbit.1.closureAtSet v.center) =
        ⟨z.1,
          v.orbit.1.closureAtSet_subset_of_mem hy z.2⟩ := by
      apply Subtype.ext
      rfl
    simpa [s, y₀, hzsub] using hzimage

/-- Every point represented by an abstract valuation lies in its physical
support. -/
theorem Valuation.physicalPoint_mem_support
    {x : β} (v : Valuation act A B₀ x)
    (z : v.orbit.1.closureAtSet v.center) :
    v.toFun z ∈
      (Valuation.physicalSignature act A B₀ v).support :=
  ⟨z, rfl⟩

/-- Restricting an abstract valuation has exactly the support obtained by
restricting its physical signature. -/
theorem Valuation.physicalSignature_restrict_support
    {x : β} (v : Valuation act A B₀ x)
    (y : α) (hy : y ∈ v.orbit.1.closureAtSet v.center) :
    (Valuation.physicalSignature act A B₀
        (Valuation.restrict act A B₀ v y hy)).support =
      ((Valuation.physicalSignature act A B₀ v).restrict
        (v.toFun ⟨y, hy⟩)
        (Valuation.physicalPoint_mem_support
          act A B₀ v ⟨y, hy⟩)).support := by
  rw [ValuationSignature.restrict_support]
  rw [Valuation.physicalSignature_closureAt_image
    act A B₀ v y hy]
  ext b
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, hb⟩
    refine ⟨z, ?_⟩
    exact hb.symm


/-- On the smaller physical closure, abstract restriction leaves physical
function values unchanged. -/
theorem Valuation.physicalFunc_restrict_of_mem
    {x : β} (v : Valuation act A B₀ x)
    (y : α) (hy : y ∈ v.orbit.1.closureAtSet v.center)
    {n : ℕ} (F : L.FuncSymbol n) (a : β)
    (ha :
      a ∈
        (Valuation.physicalSignature act A B₀ v).closureAtSet
          (v.toFun ⟨y, hy⟩)) :
    Valuation.physicalFunc act A B₀
        (Valuation.restrict act A B₀ v y hy) F a =
      Valuation.physicalFunc act A B₀ v F a := by
  let vr := Valuation.restrict act A B₀ v y hy
  have haimg :
      a ∈ Valuation.imageClosure act A B₀ v y hy := by
    rw [← Valuation.physicalSignature_closureAt_image
      act A B₀ v y hy]
    exact ha
  rcases haimg with ⟨z, hza⟩
  let z₀ : v.orbit.1.closureAtSet v.center :=
    ⟨z.1, v.orbit.1.closureAtSet_subset_of_mem hy z.2⟩
  have hzvr : vr.toFun z = a := by
    simpa [vr, z₀, Valuation.restrict] using hza.symm
  have hzv : v.toFun z₀ = a :=
    hza.symm
  ext b
  constructor
  · intro hb
    have hb' :
        b ∈ Valuation.physicalFunc act A B₀ vr F (vr.toFun z) := by
      rw [hzvr]
      exact hb
    rcases
        (Valuation.mem_physicalFunc_at_image_iff
          act A B₀ vr z F b).1 hb' with
      ⟨t, ht, hbt⟩
    have hout :
        b ∈ Valuation.physicalFunc act A B₀ v F (v.toFun z₀) := by
      apply
        (Valuation.mem_physicalFunc_at_image_iff
          act A B₀ v z₀ F b).2
      refine ⟨t, ?_, ?_⟩
      · simpa [vr, Valuation.restrict] using ht
      · simpa [vr, z₀, Valuation.restrict] using hbt
    rw [hzv] at hout
    exact hout
  · intro hb
    have hb' :
        b ∈ Valuation.physicalFunc act A B₀ v F (v.toFun z₀) := by
      rw [hzv]
      exact hb
    rcases
        (Valuation.mem_physicalFunc_at_image_iff
          act A B₀ v z₀ F b).1 hb' with
      ⟨t, ht, hbt⟩
    have hout :
        b ∈ Valuation.physicalFunc act A B₀ vr F (vr.toFun z) := by
      apply
        (Valuation.mem_physicalFunc_at_image_iff
          act A B₀ vr z F b).2
      refine ⟨t, ?_, ?_⟩
      · simpa [vr, Valuation.restrict] using ht
      · simpa [vr, z₀, Valuation.restrict] using hbt
    rw [hzvr] at hout
    exact hout

/-- Outside the smaller physical closure, the restricted abstract valuation
has no physical function values. -/
theorem Valuation.physicalFunc_restrict_of_not_mem
    {x : β} (v : Valuation act A B₀ x)
    (y : α) (hy : y ∈ v.orbit.1.closureAtSet v.center)
    {n : ℕ} (F : L.FuncSymbol n) (a : β)
    (ha :
      a ∉
        (Valuation.physicalSignature act A B₀ v).closureAtSet
          (v.toFun ⟨y, hy⟩)) :
    Valuation.physicalFunc act A B₀
        (Valuation.restrict act A B₀ v y hy) F a = ∅ := by
  ext b
  constructor
  · intro hb
    exfalso
    apply ha
    rw [Valuation.physicalSignature_closureAt_image
      act A B₀ v y hy]
    rcases hb with ⟨z, hza, t, ht, hbt⟩
    refine ⟨z, ?_⟩
    simpa [Valuation.restrict] using hza.symm
  · intro hb
    simpa using hb



/-- Forgetting an abstract restriction is exactly restriction of the physical
signature.  This combines the support and function calculations above. -/
theorem Valuation.physicalSignature_restrict
    {x : β} (v : Valuation act A B₀ x)
    (y : α) (hy : y ∈ v.orbit.1.closureAtSet v.center) :
    Valuation.physicalSignature act A B₀
        (Valuation.restrict act A B₀ v y hy) =
      (Valuation.physicalSignature act A B₀ v).restrict
        (v.toFun ⟨y, hy⟩)
        (Valuation.physicalPoint_mem_support
          act A B₀ v ⟨y, hy⟩) := by
  apply ValuationSignature.ext
  · exact Valuation.physicalSignature_restrict_support
      act A B₀ v y hy
  · funext n F a
    by_cases ha :
        a ∈
          (Valuation.physicalSignature act A B₀ v).closureAtSet
            (v.toFun ⟨y, hy⟩)
    · rw [ValuationSignature.restrict_func_of_mem
        (Valuation.physicalSignature act A B₀ v)
        (v.toFun ⟨y, hy⟩)
        (Valuation.physicalPoint_mem_support
          act A B₀ v ⟨y, hy⟩) F ha]
      exact Valuation.physicalFunc_restrict_of_mem
        act A B₀ v y hy F a ha
    · rw [ValuationSignature.restrict_func_of_not_mem
        (Valuation.physicalSignature act A B₀ v)
        (v.toFun ⟨y, hy⟩)
        (Valuation.physicalPoint_mem_support
          act A B₀ v ⟨y, hy⟩) F ha]
      exact Valuation.physicalFunc_restrict_of_not_mem
        act A B₀ v y hy F a ha

/-- Restriction is well-defined on physical valuations, independently of the
abstract presentation chosen to witness realizability. -/
noncomputable def PhysicalValuation.restrict
    {x : β} (s : PhysicalValuation act A B₀ x)
    (y : β) (hy : y ∈ s.1.support) :
    PhysicalValuation act A B₀ y := by
  refine ⟨s.1.restrict y hy, ?_⟩
  rcases s.2 with ⟨v, hv⟩
  have hyv :
      y ∈ (Valuation.physicalSignature act A B₀ v).support := by
    rw [hv]
    exact hy
  rcases hyv with ⟨z, hz⟩
  subst y
  refine
    ⟨Valuation.restrict act A B₀ v z.1 z.2, ?_⟩
  have hphys :=
    Valuation.physicalSignature_restrict
      act A B₀ v z.1 z.2
  simpa [hv] using hphys

@[simp] theorem PhysicalValuation.restrict_val
    {x : β} (s : PhysicalValuation act A B₀ x)
    (y : β) (hy : y ∈ s.1.support) :
    (PhysicalValuation.restrict act A B₀ s y hy).1 =
      s.1.restrict y hy :=
  rfl


section PhysicalWitness

/-- Vertices of the presentation-independent unary-function witness. -/
abbrev PhysicalWitnessVertex :=
  Σ x : β, PhysicalValuation act A B₀ x

def PhysicalWitnessVertex.base
    (w : PhysicalWitnessVertex act A B₀) : β :=
  w.1

def PhysicalWitnessVertex.valuation
    (w : PhysicalWitnessVertex act A B₀) :
    PhysicalValuation act A B₀ w.base :=
  w.2

/-- Every physical function value of the centre remains in the support, so its
one-point restriction is again a physical valuation. -/
theorem PhysicalWitnessVertex.funcValue_mem_support
    (w : PhysicalWitnessVertex act A B₀)
    {n : ℕ} (F : L.FuncSymbol n) {y : β}
    (hy : y ∈ w.valuation.1.func F w.base) :
    y ∈ w.valuation.1.support :=
  w.valuation.1.func_supported F w.valuation.1.center_mem hy

/-- The witness vertex corresponding to a unary function value. -/
noncomputable def physicalFunctionValueVertex
    (w : PhysicalWitnessVertex act A B₀)
    {n : ℕ} (F : L.FuncSymbol n)
    (y : β) (hy : y ∈ w.valuation.1.func F w.base) :
    PhysicalWitnessVertex act A B₀ :=
  ⟨y,
    PhysicalValuation.restrict act A B₀ w.valuation y
      (PhysicalWitnessVertex.funcValue_mem_support
        act A B₀ w F hy)⟩

@[simp] theorem physicalFunctionValueVertex_base
    (w : PhysicalWitnessVertex act A B₀)
    {n : ℕ} (F : L.FuncSymbol n)
    (y : β) (hy : y ∈ w.valuation.1.func F w.base) :
    (physicalFunctionValueVertex act A B₀ w F y hy).base = y :=
  rfl

/-- The physical unary-function witness.

Relations are read in the relational base witness.  Unary functions use the
physical function graph stored by the valuation and then restrict to the
one-point closure at the selected value. -/
noncomputable def physicalWitnessStructure :
    Structure L (PhysicalWitnessVertex act A B₀) where
  rel := by
    intro n R ws
    exact B₀.rel R (fun i => (ws i).base)
  func := by
    intro n F ws
    let w := ws (unaryIndex F)
    exact
      {z | ∃ (y : β)
        (hy : y ∈ w.valuation.1.func F w.base),
        z = physicalFunctionValueVertex act A B₀ w F y hy}

@[simp] theorem physicalWitnessStructure_rel_iff
    {n : ℕ} (R : L.RelSymbol n)
    (ws : Fin n → PhysicalWitnessVertex act A B₀) :
    (physicalWitnessStructure act A B₀).rel R ws ↔
      B₀.rel R (fun i => (ws i).base) :=
  Iff.rfl

theorem mem_physicalWitnessStructure_func_iff
    {n : ℕ} (F : L.FuncSymbol n)
    (ws : Fin n → PhysicalWitnessVertex act A B₀)
    (z : PhysicalWitnessVertex act A B₀) :
    z ∈ (physicalWitnessStructure act A B₀).func F ws ↔
      ∃ (y : β)
        (hy : y ∈
          (ws (unaryIndex F)).valuation.1.func F
            (ws (unaryIndex F)).base),
        z =
          physicalFunctionValueVertex act A B₀
            (ws (unaryIndex F)) F y hy := by
  rfl

/-- The presentation-independent witness remains finite. -/
theorem physicalWitnessVertex_finite
    (hA : A.HasFiniteRelabelOrbit act) :
    Finite (PhysicalWitnessVertex act A B₀) := by
  classical
  letI : Fintype β := Fintype.ofFinite β
  letI (x : β) : Fintype (PhysicalValuation act A B₀ x) :=
    physicalValuationFintype act A B₀ hA x
  exact Finite.of_fintype _

end PhysicalWitness

section Transport

/-- The underlying vertex permutation of a total automorphism. -/
noncomputable def automorphismEquiv
    {M : Structure L.relationalReduct β}
    (h : Structure.Automorphism act.relationalReduct M) :
    β ≃ β where
  toFun := h
  invFun := h.toPartialIsomorphism.toPartialEquiv.symm
  left_inv := by
    intro x
    have hx : x ∈ h.toPartialIsomorphism.source := by
      rw [h.source_eq_univ]
      exact Set.mem_univ x
    exact h.toPartialIsomorphism.left_inv hx
  right_inv := by
    intro x
    have hx : x ∈ h.toPartialIsomorphism.target := by
      rw [h.target_eq_univ]
      exact Set.mem_univ x
    exact h.toPartialIsomorphism.right_inv hx

@[simp] theorem automorphismEquiv_apply
    {M : Structure L.relationalReduct β}
    (h : Structure.Automorphism act.relationalReduct M) (x : β) :
    automorphismEquiv act h x = h x :=
  rfl

/-- Relabelling a valuation's orbit structure does not change the underlying
set of its one-point closure; this map only changes the subtype proof. -/
def relabelClosureToOriginal
    (g : Γ) (C : Orbit act A) (y : α)
    (z : (orbitRelabel act A g C).1.closureAtSet y) :
    C.1.closureAtSet y :=
  ⟨z.1, by
    have hz := z.2
    change z.1 ∈ (C.1.relabel act g).closureAtSet y at hz
    rw [closureAtSet_relabel act g C.1 y] at hz
    exact hz⟩

@[simp] theorem relabelClosureToOriginal_val
    (g : Γ) (C : Orbit act A) (y : α)
    (z : (orbitRelabel act A g C).1.closureAtSet y) :
    (relabelClosureToOriginal act A g C y z).1 = z.1 :=
  rfl


/-- The inverse change of subtype proof: view a point of the original
one-point closure as a point of the relabelled one-point closure. -/
def originalClosureToRelabel
    (g : Γ) (C : Orbit act A) (y : α)
    (z : C.1.closureAtSet y) :
    (orbitRelabel act A g C).1.closureAtSet y :=
  ⟨z.1, by
    change z.1 ∈ (C.1.relabel act g).closureAtSet y
    rw [closureAtSet_relabel act g C.1 y]
    exact z.2⟩

@[simp] theorem originalClosureToRelabel_val
    (g : Γ) (C : Orbit act A) (y : α)
    (z : C.1.closureAtSet y) :
    (originalClosureToRelabel act A g C y z).1 = z.1 :=
  rfl

@[simp] theorem relabelClosureToOriginal_originalClosureToRelabel
    (g : Γ) (C : Orbit act A) (y : α)
    (z : C.1.closureAtSet y) :
    relabelClosureToOriginal act A g C y
        (originalClosureToRelabel act A g C y z) = z := by
  apply Subtype.ext
  rfl

@[simp] theorem originalClosureToRelabel_relabelClosureToOriginal
    (g : Γ) (C : Orbit act A) (y : α)
    (z : (orbitRelabel act A g C).1.closureAtSet y) :
    originalClosureToRelabel act A g C y
        (relabelClosureToOriginal act A g C y z) = z := by
  apply Subtype.ext
  rfl

/-- Transport an abstract finite valuation presentation along a total
automorphism of the relational base witness.  The language component is
absorbed by relabelling the abstract orbit structure. -/
noncomputable def Valuation.transport
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (v : Valuation act A B₀ x) :
    Valuation act A B₀ (h x) where
  orbit := orbitRelabel act A h.lang v.orbit
  center := v.center
  toFun := fun z =>
    h (v.toFun
      (relabelClosureToOriginal act A h.lang v.orbit v.center z))
  injective := by
    intro z z' hzz
    have hh :
        v.toFun
            (relabelClosureToOriginal act A h.lang v.orbit v.center z) =
          v.toFun
            (relabelClosureToOriginal act A h.lang v.orbit v.center z') := by
      exact (automorphismEquiv act h).injective hzz
    have hz :
        relabelClosureToOriginal act A h.lang v.orbit v.center z =
          relabelClosureToOriginal act A h.lang v.orbit v.center z' :=
      v.injective hh
    apply Subtype.ext
    simpa using
      congrArg
        (fun t : v.orbit.1.closureAtSet v.center => t.1) hz
  map_rel_iff := by
    intro n R xs
    let oldxs : Fin n → v.orbit.1.closureAtSet v.center :=
      fun i =>
        relabelClosureToOriginal act A h.lang v.orbit v.center (xs i)
    let S : L.RelSymbol n := act.onRel h.lang⁻¹ R
    have hall :
        ∀ i,
          v.toFun (oldxs i) ∈ h.toPartialIsomorphism.source := by
      intro i
      rw [h.source_eq_univ]
      exact Set.mem_univ _
    have hh :=
      h.toPartialIsomorphism.map_rel_iff S
        (fun i => v.toFun (oldxs i)) hall
    change
      B₀.rel (act.relationalReduct.onRel h.lang S)
          (h.toPartialIsomorphism.toPartialEquiv ∘
            fun i => v.toFun (oldxs i)) ↔
        B₀.rel S (fun i => v.toFun (oldxs i)) at hh
    have hsym :
        act.relationalReduct.onRel h.lang S = R := by
      change act.onRel h.lang S = R
      simp [S, ← Language.Action.onRel_mul]
    rw [hsym] at hh
    have hv := v.map_rel_iff S oldxs
    change
      B₀.rel R
          (fun i =>
            h (v.toFun
              (relabelClosureToOriginal act A h.lang
                v.orbit v.center (xs i)))) ↔
        (v.orbit.1.relabel act h.lang).rel R
          (fun i => (xs i).1)
    have hchain :
        B₀.rel R (fun i => h (v.toFun (oldxs i))) ↔
          v.orbit.1.rel S (Subtype.val ∘ oldxs) :=
      hh.trans hv
    simpa [oldxs, S, Structure.relabel_rel, Function.comp_def] using hchain
  center_eq := by
    change
      h
          (v.toFun
            (relabelClosureToOriginal act A h.lang v.orbit v.center
              ⟨v.center,
                (orbitRelabel act A h.lang v.orbit).1.mem_closureAtSet
                  v.center⟩)) =
        h x
    congr 1
    have hz :
        relabelClosureToOriginal act A h.lang v.orbit v.center
            ⟨v.center,
              (orbitRelabel act A h.lang v.orbit).1.mem_closureAtSet
                v.center⟩ =
          ⟨v.center, v.orbit.1.mem_closureAtSet v.center⟩ := by
      apply Subtype.ext
      rfl
    rw [hz, v.center_eq]

/-- Physical transport of a valuation signature.  It is literal conjugation:
move the support by the base permutation and transport each unary function
graph, while relabelling the function symbol by the language component. -/
noncomputable def ValuationSignature.transport
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (s : ValuationSignature (L := L) x) :
    ValuationSignature (L := L) (h x) := by
  classical
  let e := automorphismEquiv act h
  refine
    { support := h '' s.support
      center_mem := ⟨x, s.center_mem, rfl⟩
      func := fun F a =>
        h '' s.func (act.onFunc h.lang⁻¹ F) (e.symm a)
      func_supported := ?_ }
  intro n F a ha b hb
  rcases ha with ⟨d, hd, hda⟩
  have hpre : e.symm a = d := by
    apply e.injective
    simpa [e, hda]
  rcases hb with ⟨c, hc, hcb⟩
  refine ⟨c, ?_, hcb⟩
  apply s.func_supported (act.onFunc h.lang⁻¹ F) hd
  simpa [hpre] using hc

@[simp] theorem ValuationSignature.transport_support
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (s : ValuationSignature (L := L) x) :
    (s.transport act B₀ h).support = h '' s.support :=
  rfl



@[simp] theorem ValuationSignature.transport_func
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (s : ValuationSignature (L := L) x)
    {n : ℕ} (F : L.FuncSymbol n) (a : β) :
    (s.transport act B₀ h).func F a =
      h '' s.func (act.onFunc h.lang⁻¹ F)
        ((automorphismEquiv act h).symm a) :=
  rfl

/-- Conjugating a physical signature by a base automorphism is injective. -/
theorem ValuationSignature.transport_injective
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} :
    Function.Injective
      (ValuationSignature.transport act B₀ h :
        ValuationSignature (L := L) x →
          ValuationSignature (L := L) (h x)) := by
  intro s t hst
  apply ValuationSignature.ext
  · have hs := congrArg ValuationSignature.support hst
    change h '' s.support = h '' t.support at hs
    exact (Set.image_injective.mpr
      (automorphismEquiv act h).injective) hs
  · funext n F a
    have hf :=
      congrArg
        (fun q : ValuationSignature (L := L) (h x) =>
          q.func (act.onFunc h.lang F) (h a)) hst
    have himage :
        h '' s.func F a = h '' t.func F a := by
      simpa [ValuationSignature.transport_func,
        ← Language.Action.onFunc_mul] using hf
    exact (Set.image_injective.mpr
      (automorphismEquiv act h).injective) himage

/-- Abstract transport moves the physical support exactly by the underlying
base automorphism. -/
theorem Valuation.physicalSignature_transport_support
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (v : Valuation act A B₀ x) :
    (Valuation.physicalSignature act A B₀
        (Valuation.transport act A B₀ h v)).support =
      (ValuationSignature.transport act B₀ h
        (Valuation.physicalSignature act A B₀ v)).support := by
  change
    Set.range
        (fun z =>
          h (v.toFun
            (relabelClosureToOriginal act A h.lang
              v.orbit v.center z))) =
      h '' Set.range v.toFun
  ext b
  constructor
  · rintro ⟨z, rfl⟩
    exact
      ⟨v.toFun
          (relabelClosureToOriginal act A h.lang
            v.orbit v.center z),
        ⟨relabelClosureToOriginal act A h.lang
          v.orbit v.center z, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨z, rfl⟩, rfl⟩
    refine
      ⟨originalClosureToRelabel act A h.lang
          v.orbit v.center z, ?_⟩
    simp


/-- Abstract valuation transport also gives exactly the conjugated physical
unary-function values. -/
theorem Valuation.physicalFunc_transport
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (v : Valuation act A B₀ x)
    {n : ℕ} (F : L.FuncSymbol n) (a : β) :
    Valuation.physicalFunc act A B₀
        (Valuation.transport act A B₀ h v) F a =
      h '' Valuation.physicalFunc act A B₀ v
        (act.onFunc h.lang⁻¹ F)
        ((automorphismEquiv act h).symm a) := by
  classical
  let e := automorphismEquiv act h
  ext b
  constructor
  · intro hb
    rcases hb with ⟨z, hza, y, hy, hby⟩
    let z₀ : v.orbit.1.closureAtSet v.center :=
      relabelClosureToOriginal act A h.lang v.orbit v.center z
    have hza₀ : v.toFun z₀ = e.symm a := by
      change e (v.toFun z₀) = a at hza
      have hz := congrArg e.symm hza
      simpa using hz
    have hy₀ :
        y ∈ v.orbit.1.func (act.onFunc h.lang⁻¹ F)
          (fun _ => z₀.1) := by
      change
        y ∈ (v.orbit.1.relabel act h.lang).func F
          (fun _ => z.1) at hy
      have htuple :
          (fun _ : Fin n => z₀.1) =
            (fun _ : Fin n => z.1) := by
        funext i
        rfl
      rw [htuple]
      simpa [Structure.relabel_func] using hy
    have hycl :
        y ∈ v.orbit.1.closureAtSet v.center :=
      Valuation.func_mem_closure_of_mem act A B₀ v z₀
        (act.onFunc h.lang⁻¹ F) hy₀
    let c₀ : β := v.toFun ⟨y, hycl⟩
    refine ⟨c₀, ?_, ?_⟩
    · refine ⟨z₀, hza₀, y, hy₀, ?_⟩
      rfl
    · rw [hby]
      change
        h c₀ =
          h
            (v.toFun
              (relabelClosureToOriginal act A h.lang
                v.orbit v.center
                ⟨y,
                  Valuation.func_mem_closure_of_mem act A B₀
                    (Valuation.transport act A B₀ h v) z F hy⟩))
      apply congrArg h
      apply congrArg v.toFun
      apply Subtype.ext
      rfl
  · intro hb
    rcases hb with ⟨c₀, hc₀, hcb⟩
    rcases hc₀ with ⟨z₀, hza₀, y, hy₀, hcy⟩
    let z :=
      originalClosureToRelabel act A h.lang v.orbit v.center z₀
    have hza :
        h
            (v.toFun
              (relabelClosureToOriginal act A h.lang
                v.orbit v.center z)) = a := by
      rw [show
        relabelClosureToOriginal act A h.lang
            v.orbit v.center z = z₀ by
          simp [z]]
      change e (v.toFun z₀) = a
      rw [hza₀]
      exact e.apply_symm_apply a
    have hy :
        y ∈ (v.orbit.1.relabel act h.lang).func F
          (fun _ => z.1) := by
      simpa [z, Structure.relabel_func] using hy₀
    refine ⟨z, hza, y, hy, ?_⟩
    calc
      b = h c₀ := hcb.symm
      _ =
          h
            (v.toFun
              ⟨y,
                Valuation.func_mem_closure_of_mem act A B₀ v z₀
                  (act.onFunc h.lang⁻¹ F) hy₀⟩) :=
        congrArg h hcy
      _ =
          h
            (v.toFun
              (relabelClosureToOriginal act A h.lang
                v.orbit v.center
                ⟨y,
                  Valuation.func_mem_closure_of_mem act A B₀
                    (Valuation.transport act A B₀ h v) z F hy⟩)) := by
        apply congrArg h
        apply congrArg v.toFun
        apply Subtype.ext
        rfl

/-- Transport commutes with forgetting an abstract valuation presentation.
This is the key descent statement to the quotient by physical signatures. -/
theorem Valuation.physicalSignature_transport
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (v : Valuation act A B₀ x) :
    Valuation.physicalSignature act A B₀
        (Valuation.transport act A B₀ h v) =
      ValuationSignature.transport act B₀ h
        (Valuation.physicalSignature act A B₀ v) := by
  apply ValuationSignature.ext
  · exact Valuation.physicalSignature_transport_support act A B₀ h v
  · funext n F a
    exact Valuation.physicalFunc_transport act A B₀ h v F a

/-- The base automorphism acts canonically on physical valuations; the
previous theorem shows that this is independent of the chosen abstract
presentation. -/
noncomputable def PhysicalValuation.transport
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (s : PhysicalValuation act A B₀ x) :
    PhysicalValuation act A B₀ (h x) := by
  refine
    ⟨ValuationSignature.transport act B₀ h s.1, ?_⟩
  rcases s.2 with ⟨v, hv⟩
  refine
    ⟨Valuation.transport act A B₀ h v, ?_⟩
  calc
    Valuation.physicalSignature act A B₀
        (Valuation.transport act A B₀ h v) =
        ValuationSignature.transport act B₀ h
          (Valuation.physicalSignature act A B₀ v) :=
      Valuation.physicalSignature_transport act A B₀ h v
    _ =
        ValuationSignature.transport act B₀ h s.1 :=
      congrArg (ValuationSignature.transport act B₀ h) hv

@[simp] theorem PhysicalValuation.transport_val
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (s : PhysicalValuation act A B₀ x) :
    (PhysicalValuation.transport act A B₀ h s).1 =
      ValuationSignature.transport act B₀ h s.1 :=
  rfl

/-- Transport on realised physical valuations is injective. -/
theorem PhysicalValuation.transport_injective
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} :
    Function.Injective
      (PhysicalValuation.transport act A B₀ h :
        PhysicalValuation act A B₀ x →
          PhysicalValuation act A B₀ (h x)) := by
  intro s t hst
  apply Subtype.ext
  apply ValuationSignature.transport_injective act B₀ h
  exact congrArg Subtype.val hst



/-- One-point closure is equivariant under conjugation by a base
automorphism. -/
theorem ValuationSignature.transport_closureAtSet
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (s : ValuationSignature (L := L) x)
    (y : β) :
    (s.transport act B₀ h).closureAtSet (h y) =
      h '' s.closureAtSet y := by
  let e := automorphismEquiv act h
  let t := s.transport act B₀ h
  apply Set.Subset.antisymm
  · apply t.closureSet_minimal
    · intro n F a ha b hb
      rcases ha with ⟨d, hd, rfl⟩
      have hpre : e.symm (h d) = d := by
        exact e.symm_apply_apply d
      rw [ValuationSignature.transport_func] at hb
      rw [hpre] at hb
      rcases hb with ⟨c, hc, rfl⟩
      refine ⟨c, ?_, rfl⟩
      exact
        (s.isClosed_closureSet {y})
          (act.onFunc h.lang⁻¹ F) hd hc
    · intro a ha
      have hay : a = h y := by
        simpa using ha
      subst a
      exact ⟨y, s.mem_closureAtSet y, rfl⟩
  · rintro b ⟨c, hc, rfl⟩
    let T : Set β :=
      {d | h d ∈ t.closureAtSet (h y)}
    have hTclosed : s.IsClosed T := by
      intro n F a ha b hb
      have hpre : e.symm (h a) = a :=
        e.symm_apply_apply a
      have hphys :
          h b ∈ t.func (act.onFunc h.lang F) (h a) := by
        rw [ValuationSignature.transport_func]
        rw [hpre]
        have hsym :
            act.onFunc h.lang⁻¹
                (act.onFunc h.lang F) = F := by
          rw [← Language.Action.onFunc_mul]
          simp
        rw [hsym]
        exact ⟨b, hb, rfl⟩
      exact
        (t.isClosed_closureSet {h y})
          (act.onFunc h.lang F) ha hphys
    have hyT : y ∈ T :=
      t.mem_closureAtSet (h y)
    have hsingle : ({y} : Set β) ⊆ T := by
      intro a ha
      have hay : a = y := by simpa using ha
      subst a
      exact hyT
    exact (s.closureSet_minimal hTclosed hsingle) hc

/-- Transport commutes with restricting a physical signature to a supported
point. -/
theorem ValuationSignature.transport_restrict
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (s : ValuationSignature (L := L) x)
    (y : β) (hy : y ∈ s.support) :
    (s.restrict y hy).transport act B₀ h =
      (s.transport act B₀ h).restrict (h y)
        ⟨y, hy, rfl⟩ := by
  let e := automorphismEquiv act h
  apply ValuationSignature.ext
  · rw [ValuationSignature.transport_support,
      ValuationSignature.restrict_support,
      ValuationSignature.restrict_support,
      ValuationSignature.transport_closureAtSet]
  · funext n F a
    by_cases ha :
        a ∈ (s.transport act B₀ h).closureAtSet (h y)
    · have hpre :
          e.symm a ∈ s.closureAtSet y := by
        rw [ValuationSignature.transport_closureAtSet] at ha
        rcases ha with ⟨d, hd, hda⟩
        have hed : e.symm a = d := by
          apply e.injective
          simpa [e, hda]
        simpa [hed] using hd
      rw [ValuationSignature.restrict_func_of_mem
        (s.transport act B₀ h) (h y) ⟨y, hy, rfl⟩ F ha]
      rw [ValuationSignature.transport_func]
      rw [ValuationSignature.restrict_func_of_mem
        s y hy (act.onFunc h.lang⁻¹ F) hpre]
      rfl
    · have hpre :
          e.symm a ∉ s.closureAtSet y := by
        intro hmem
        apply ha
        rw [ValuationSignature.transport_closureAtSet]
        refine ⟨e.symm a, hmem, ?_⟩
        exact e.apply_symm_apply a
      rw [ValuationSignature.restrict_func_of_not_mem
        (s.transport act B₀ h) (h y) ⟨y, hy, rfl⟩ F ha]
      rw [ValuationSignature.transport_func]
      rw [ValuationSignature.restrict_func_of_not_mem
        s y hy (act.onFunc h.lang⁻¹ F) hpre]
      simp

/-- The same commutation law descends to realised physical valuations. -/
theorem PhysicalValuation.transport_restrict
    (h : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (s : PhysicalValuation act A B₀ x)
    (y : β) (hy : y ∈ s.1.support) :
    PhysicalValuation.transport act A B₀ h
        (PhysicalValuation.restrict act A B₀ s y hy) =
      PhysicalValuation.restrict act A B₀
        (PhysicalValuation.transport act A B₀ h s)
        (h y) ⟨y, hy, rfl⟩ := by
  apply Subtype.ext
  exact ValuationSignature.transport_restrict act B₀ h s.1 y hy

/-- Transport a whole physical witness vertex along a base automorphism. -/
noncomputable def PhysicalWitnessVertex.transport
    (h : Structure.Automorphism act.relationalReduct B₀)
    (w : PhysicalWitnessVertex act A B₀) :
    PhysicalWitnessVertex act A B₀ :=
  Sigma.map h
    (fun _ => PhysicalValuation.transport act A B₀ h) w

@[simp] theorem PhysicalWitnessVertex.transport_base
    (h : Structure.Automorphism act.relationalReduct B₀)
    (w : PhysicalWitnessVertex act A B₀) :
    (PhysicalWitnessVertex.transport act A B₀ h w).base =
      h w.base :=
  rfl

/-- Transport of witness vertices is injective fibrewise and on the base. -/
theorem PhysicalWitnessVertex.transport_injective
    (h : Structure.Automorphism act.relationalReduct B₀) :
    Function.Injective
      (PhysicalWitnessVertex.transport act A B₀ h) := by
  exact
    (automorphismEquiv act h).injective.sigma_map
      (fun x => PhysicalValuation.transport_injective act A B₀ h)

/-- Because the physical witness is finite, its injective transport map is a
permutation. -/
noncomputable def physicalWitnessEquiv
    (hA : A.HasFiniteRelabelOrbit act)
    (h : Structure.Automorphism act.relationalReduct B₀) :
    PhysicalWitnessVertex act A B₀ ≃
      PhysicalWitnessVertex act A B₀ := by
  let f := PhysicalWitnessVertex.transport act A B₀ h
  have hf : Function.Injective f :=
    PhysicalWitnessVertex.transport_injective act A B₀ h
  letI : Finite (PhysicalWitnessVertex act A B₀) :=
    physicalWitnessVertex_finite act A B₀ hA
  have hs : Function.Surjective f :=
    Finite.injective_iff_surjective.mp hf
  exact Equiv.ofBijective f ⟨hf, hs⟩

@[simp] theorem physicalWitnessEquiv_apply
    (hA : A.HasFiniteRelabelOrbit act)
    (h : Structure.Automorphism act.relationalReduct B₀)
    (w : PhysicalWitnessVertex act A B₀) :
    physicalWitnessEquiv act A B₀ hA h w =
      PhysicalWitnessVertex.transport act A B₀ h w :=
  rfl


/-- At the centre of a transported physical valuation, the relabelled
function values are exactly the images of the old function values. -/
theorem PhysicalWitnessVertex.transport_center_func
    (h : Structure.Automorphism act.relationalReduct B₀)
    (w : PhysicalWitnessVertex act A B₀)
    {n : ℕ} (F : L.FuncSymbol n) :
    (PhysicalWitnessVertex.transport act A B₀ h w).valuation.1.func
        (act.onFunc h.lang F) (h w.base) =
      h '' w.valuation.1.func F w.base := by
  change
    (ValuationSignature.transport act B₀ h w.valuation.1).func
        (act.onFunc h.lang F) (h w.base) =
      h '' w.valuation.1.func F w.base
  rw [ValuationSignature.transport_func]
  have hpre :
      (automorphismEquiv act h).symm (h w.base) = w.base :=
    (automorphismEquiv act h).symm_apply_apply w.base
  rw [hpre]
  have hsym :
      act.onFunc h.lang⁻¹ (act.onFunc h.lang F) = F := by
    rw [← Language.Action.onFunc_mul]
    simp
  rw [hsym]

/-- The lifted witness permutation preserves and reflects every relation. -/
theorem physicalWitnessRelation_transport_iff
    (hA : A.HasFiniteRelabelOrbit act)
    (h : Structure.Automorphism act.relationalReduct B₀)
    {n : ℕ} (R : L.RelSymbol n)
    (ws : Fin n → PhysicalWitnessVertex act A B₀) :
    (physicalWitnessStructure act A B₀).rel
        (act.onRel h.lang R)
        (physicalWitnessEquiv act A B₀ hA h ∘ ws) ↔
      (physicalWitnessStructure act A B₀).rel R ws := by
  have hall :
      ∀ i, (ws i).base ∈ h.toPartialIsomorphism.source := by
    intro i
    rw [h.source_eq_univ]
    exact Set.mem_univ _
  have hh :=
    h.toPartialIsomorphism.map_rel_iff R
      (fun i => (ws i).base) hall
  change
    B₀.rel (act.onRel h.lang R)
        (fun i => h (ws i).base) ↔
      B₀.rel R (fun i => (ws i).base)
  simpa [Function.comp_def, physicalWitnessEquiv_apply,
    PhysicalWitnessVertex.transport, PhysicalWitnessVertex.base] using hh

end Transport

end PhysicalValuations

end UnaryFunctions
end AllThoseEPPA
