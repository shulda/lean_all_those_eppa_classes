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
          (Subtype.val ∘ xs)
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

end Transport

end PhysicalValuations

end UnaryFunctions
end AllThoseEPPA
