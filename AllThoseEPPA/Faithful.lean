import AllThoseEPPA.Irreducible
import AllThoseEPPA.UnaryFunctions

/-!
# Irreducible-structure faithful EPPA

This file formalizes Proposition `prop:faithful`.  We begin with the finite
valuation data used by the faithful witness construction.

The paper labels a bad irreducible structure `I` by
`{1, ..., |I|-1}`.  Here we use the equivalent label set obtained by choosing
one vertex of `I` outside the distinguished copy of `A` and deleting it.
This makes the canonical valuations on `A` literal: a vertex is labelled by
its own image in `B₀`.
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w z

variable {L : Language.{u}}
variable {Γ : Type w} [Group Γ]
variable {α : Type v}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)

/-- An irreducible substructure of `B₀` is bad if no automorphism of `B₀`
moves it wholly into the distinguished copy `ψ(A)`. -/
structure BadIrreducible where
  carrier : Set β
  closed : B₀.IsClosed carrier
  irreducible : (B₀.induce carrier closed).IsIrreducible
  bad :
    ¬ ∃ g : Structure.Automorphism act B₀,
      ∀ x, x ∈ carrier → ∃ a : α, g x = ψ a

namespace BadIrreducible

@[ext] theorem ext
    {I J : BadIrreducible act A B₀ ψ}
    (h : I.carrier = J.carrier) :
    I = J := by
  cases I
  cases J
  cases h
  rfl

/-- There are only finitely many bad irreducible substructures of a finite
base witness. -/
theorem finite [Finite β] :
    Finite (BadIrreducible act A B₀ ψ) := by
  apply Finite.of_injective
    (fun I : BadIrreducible act A B₀ ψ => I.carrier)
  intro I J h
  exact BadIrreducible.ext h

/-- Every bad irreducible contains a vertex outside the distinguished copy of
`A`: otherwise the identity automorphism would already move it into that
copy. -/
theorem exists_not_mem_range
    (I : BadIrreducible act A B₀ ψ) :
    ∃ x : β, x ∈ I.carrier ∧ x ∉ Set.range ψ := by
  by_contra h
  apply I.bad
  refine ⟨Structure.Automorphism.id B₀, ?_⟩
  intro x hx
  have hrange : x ∈ Set.range ψ := by
    by_contra hxr
    exact h ⟨x, hx, hxr⟩
  rcases hrange with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [ha]

/-- A distinguished omitted vertex of a bad irreducible structure. -/
noncomputable def hole
    (I : BadIrreducible act A B₀ ψ) : β :=
  Classical.choose (I.exists_not_mem_range act A B₀ ψ)

theorem hole_mem
    (I : BadIrreducible act A B₀ ψ) :
    I.hole act A B₀ ψ ∈ I.carrier :=
  (Classical.choose_spec
    (I.exists_not_mem_range act A B₀ ψ)).1

theorem hole_not_mem_range
    (I : BadIrreducible act A B₀ ψ) :
    I.hole act A B₀ ψ ∉ Set.range ψ :=
  (Classical.choose_spec
    (I.exists_not_mem_range act A B₀ ψ)).2

end BadIrreducible

/-- Labels available on a bad irreducible `I`: all its vertices except for
the distinguished hole.  This has exactly `|I|-1` elements, matching the
paper's label set, but avoids cardinal arithmetic in the construction. -/
abbrev BadLabel
    (I : BadIrreducible act A B₀ ψ) :=
  {x : β // x ∈ I.carrier ∧
    x ≠ I.hole act A B₀ ψ}

/-- Bad irreducibles containing a fixed base vertex. -/
abbrev BadAt (x : β) :=
  {I : BadIrreducible act A B₀ ψ // x ∈ I.carrier}

/-- A valuation function for a base vertex. -/
abbrev ValuationFunction (x : β) :=
  (I : BadAt act A B₀ ψ x) → BadLabel act A B₀ ψ I.1

/-- Valuation functions form a finite type over a finite base witness. -/
theorem valuationFunction_finite [Finite β] (x : β) :
    Finite (ValuationFunction act A B₀ ψ x) := by
  letI : Finite (BadIrreducible act A B₀ ψ) :=
    BadIrreducible.finite act A B₀ ψ
  infer_instance

/-- A base point together with one of its valuation functions. -/
abbrev ValuationPoint :=
  Σ x : β, ValuationFunction act A B₀ ψ x

/-- Genericity of two valuation points.  Equal points are allowed; distinct
base points must receive different labels on every bad irreducible containing
both. -/
def AreGeneric
    (p q : ValuationPoint act A B₀ ψ) : Prop :=
  p = q ∨
    (p.1 ≠ q.1 ∧
      ∀ (I : BadIrreducible act A B₀ ψ)
        (hp : p.1 ∈ I.carrier) (hq : q.1 ∈ I.carrier),
        (p.2 ⟨I, hp⟩).1 ≠ (q.2 ⟨I, hq⟩).1)

/-- A set of valuation points is generic when every pair in it is generic. -/
def IsGeneric
    (S : Set (ValuationPoint act A B₀ ψ)) : Prop :=
  ∀ ⦃p⦄, p ∈ S → ∀ ⦃q⦄, q ∈ S → AreGeneric act A B₀ ψ p q

theorem areGeneric_refl
    (p : ValuationPoint act A B₀ ψ) :
    AreGeneric act A B₀ ψ p p :=
  Or.inl rfl

theorem areGeneric_symm
    {p q : ValuationPoint act A B₀ ψ}
    (h : AreGeneric act A B₀ ψ p q) :
    AreGeneric act A B₀ ψ q p := by
  rcases h with rfl | ⟨hpq, hlabels⟩
  · exact areGeneric_refl act A B₀ ψ p
  · refine Or.inr ⟨Ne.symm hpq, ?_⟩
    intro I hq hp
    exact Ne.symm (hlabels I hp hq)

/-- On the distinguished copy of `A`, the canonical valuation at a base
vertex uses that base vertex itself as every bad-irreducible label. -/
noncomputable def canonicalValuationFunction
    (x : β) (hx : x ∈ Set.range ψ) :
    ValuationFunction act A B₀ ψ x :=
  fun I =>
    ⟨x, I.2, by
      intro h
      apply I.1.hole_not_mem_range act A B₀ ψ
      simpa [h] using hx⟩

/-- Canonical valuation points belonging to the distinguished copy are
pairwise generic. -/
theorem canonical_areGeneric
    {x y : β}
    (hx : x ∈ Set.range ψ) (hy : y ∈ Set.range ψ) :
    AreGeneric act A B₀ ψ
      ⟨x, canonicalValuationFunction act A B₀ ψ x hx⟩
      ⟨y, canonicalValuationFunction act A B₀ ψ y hy⟩ := by
  by_cases hxy : x = y
  · subst y
    left
    have hproof : hx = hy := Subsingleton.elim _ _
    subst hy
    rfl
  · right
    refine ⟨hxy, ?_⟩
    intro I hxI hyI
    change x ≠ y
    exact hxy


/-- An embedding has a function-closed range. -/
theorem embedding_range_isClosed
    (f : Structure.Embedding act A B₀) :
    B₀.IsClosed (Set.range f) := by
  classical
  intro n F xs hxs y hy
  choose as has using hxs
  have htuple : f.toFun ∘ as = xs := by
    funext i
    exact has i
  have hy' :
      y ∈ B₀.func (act.onFunc f.lang F) (f.toFun ∘ as) := by
    rw [htuple]
    exact hy
  rw [← f.map_func F as] at hy'
  rcases hy' with ⟨a, ha, hfa⟩
  exact ⟨a, hfa⟩

/-- The one-point closure of a vertex in an embedded copy remains in that
copy. -/
theorem closureAtSet_subset_embedding_range
    (f : Structure.Embedding act A B₀)
    {x : β} (hx : x ∈ Set.range f) :
    B₀.closureAtSet x ⊆ Set.range f := by
  apply B₀.closureSet_minimal (embedding_range_isClosed act A B₀ f)
  intro y hy
  have hyx : y = x := by simpa using hy
  subst y
  exact hx

/-- A valuation assignment over the one-point closure of a base vertex. -/
abbrev ValuationAssignment (x : β) :=
  ∀ y : B₀.closureAtSet x,
    ValuationFunction act A B₀ ψ y.1

/-- The valuation point selected at a member of a one-point closure. -/
def valuationPointAt
    {x : β} (v : ValuationAssignment act A B₀ ψ x)
    (y : B₀.closureAtSet x) :
    ValuationPoint act A B₀ ψ :=
  ⟨y.1, v y⟩

/-- Genericity of all valuation points occurring in one valuation
assignment. -/
def IsGenericAssignment
    {x : β} (v : ValuationAssignment act A B₀ ψ x) : Prop :=
  ∀ y z : B₀.closureAtSet x,
    AreGeneric act A B₀ ψ
      (valuationPointAt act A B₀ ψ v y)
      (valuationPointAt act A B₀ ψ v z)

/-- A valuation structure over `x`, normalized to the data that matter:
one valuation function above every point of `cl_{B₀}(x)`, with generic
total graph.  The actual structure is uniquely recovered via projection to
the closure, so carrying it separately would only add proof bureaucracy. -/
abbrev ValuationStructure (x : β) :=
  {v : ValuationAssignment act A B₀ ψ x //
    IsGenericAssignment act A B₀ ψ v}

/-- Valuation structures over a point form a finite type whenever the base
witness is finite. -/
theorem valuationStructure_finite [Finite β] (x : β) :
    Finite (ValuationStructure act A B₀ ψ x) := by
  letI (y : B₀.closureAtSet x) :
      Finite (ValuationFunction act A B₀ ψ y.1) :=
    valuationFunction_finite act A B₀ ψ y.1
  infer_instance

/-- Inclusion of a smaller one-point closure into a larger one. -/
def closureInclusion
    {x y : β} (hy : y ∈ B₀.closureAtSet x)
    (z : B₀.closureAtSet y) :
    B₀.closureAtSet x :=
  ⟨z.1, B₀.closureAtSet_subset_of_mem hy z.2⟩

/-- Restrict a valuation structure to the one-point closure of one of its
points. -/
def ValuationStructure.restrict
    {x : β} (V : ValuationStructure act A B₀ ψ x)
    (y : β) (hy : y ∈ B₀.closureAtSet x) :
    ValuationStructure act A B₀ ψ y :=
  ⟨fun z => V.1 (closureInclusion act A B₀ ψ hy z),
    by
      intro z z'
      exact V.2
        (closureInclusion act A B₀ ψ hy z)
        (closureInclusion act A B₀ ψ hy z')⟩

/-- Vertices of the faithful witness. -/
abbrev WitnessVertex :=
  Σ x : β, ValuationStructure act A B₀ ψ x

def WitnessVertex.base
    (w : WitnessVertex act A B₀ ψ) : β :=
  w.1

def WitnessVertex.valuation
    (w : WitnessVertex act A B₀ ψ) :
    ValuationStructure act A B₀ ψ w.base :=
  w.2

/-- The valuation point of a witness vertex corresponding to an arbitrary
point of its one-point closure. -/
def WitnessVertex.pointAt
    (w : WitnessVertex act A B₀ ψ)
    (y : B₀.closureAtSet w.base) :
    ValuationPoint act A B₀ ψ :=
  valuationPointAt act A B₀ ψ w.valuation.1 y

/-- A family of witness vertices is generic when the union of all valuation
structures appearing in it is generic, exactly as in the paper. -/
def WitnessFamilyGeneric
    {ι : Type*} (ws : ι → WitnessVertex act A B₀ ψ) : Prop :=
  ∀ i j (y : B₀.closureAtSet (ws i).base)
      (z : B₀.closureAtSet (ws j).base),
    AreGeneric act A B₀ ψ
      ((ws i).pointAt act A B₀ ψ y)
      ((ws j).pointAt act A B₀ ψ z)

/-- Function values at a constant tuple belong to the one-point closure of
the constant vertex. -/
theorem func_mem_closureAtSet
    {x y : β} {n : ℕ} (F : L.FuncSymbol n)
    (hy : y ∈ B₀.func F (fun _ => x)) :
    y ∈ B₀.closureAtSet x := by
  change y ∈ B₀.closureSet {x}
  exact
    (B₀.isClosed_closureSet ({x} : Set β))
      F (fun _ => x) (fun _ => B₀.mem_closureAtSet x) hy

/-- Witness vertex attached to a unary function value. -/
def functionValueVertex
    (w : WitnessVertex act A B₀ ψ)
    {n : ℕ} (F : L.FuncSymbol n)
    (y : β) (hy : y ∈ B₀.func F (fun _ => w.base)) :
    WitnessVertex act A B₀ ψ :=
  ⟨y,
    w.valuation.restrict act A B₀ ψ y
      (func_mem_closureAtSet act A B₀ F hy)⟩

section UnaryWitness

variable [L.HasUnaryFunctions]

/-- The normalized irreducible-faithful witness construction. -/
noncomputable def witnessStructure :
    Structure L (WitnessVertex act A B₀ ψ) where
  rel := by
    intro n R ws
    exact
      B₀.rel R (fun i => (ws i).base) ∧
        WitnessFamilyGeneric act A B₀ ψ ws
  func := by
    intro n F ws
    let w := ws (UnaryFunctions.unaryIndex F)
    exact
      {z | ∃ (y : β)
        (hy : y ∈ B₀.func F (fun _ => w.base)),
        z = functionValueVertex act A B₀ ψ w F y hy}

/-- The faithful witness has finite carrier over a finite base witness. -/
theorem witnessVertex_finite [Finite β] :
    Finite (WitnessVertex act A B₀ ψ) := by
  letI (x : β) : Finite (ValuationStructure act A B₀ ψ x) :=
    valuationStructure_finite act A B₀ ψ x
  infer_instance

end UnaryWitness

/-- Canonical valuation structure over a point of the distinguished embedded
copy.  Every point of its closure is again in the embedded copy and labels
itself. -/
noncomputable def canonicalValuationStructure
    (x : β) (hx : x ∈ Set.range ψ) :
    ValuationStructure act A B₀ ψ x := by
  let hsub :
      B₀.closureAtSet x ⊆ Set.range ψ :=
    closureAtSet_subset_embedding_range act A B₀ ψ hx
  refine
    ⟨fun y =>
      canonicalValuationFunction act A B₀ ψ y.1 (hsub y.2),
      ?_⟩
  intro y z
  exact
    canonical_areGeneric act A B₀ ψ
      (hsub y.2) (hsub z.2)

/-- Canonical witness vertex representing a vertex of `A`. -/
noncomputable def canonicalVertex (a : α) :
    WitnessVertex act A B₀ ψ :=
  ⟨ψ a,
    canonicalValuationStructure act A B₀ ψ
      (ψ a) ⟨a, rfl⟩⟩


/-- The canonical valuation function depends only on the base vertex, not on
the proof that the vertex lies in the distinguished copy. -/
theorem canonicalValuationFunction_proof_irrel
    {x : β} (hx hy : x ∈ Set.range ψ) :
    canonicalValuationFunction act A B₀ ψ x hx =
      canonicalValuationFunction act A B₀ ψ x hy := by
  have h : hx = hy := Subsingleton.elim _ _
  subst hy
  rfl

/-- Restricting a canonical valuation structure gives the canonical
valuation structure at the new centre. -/
theorem canonicalValuationStructure_restrict
    {x y : β}
    (hx : x ∈ Set.range ψ)
    (hy : y ∈ B₀.closureAtSet x)
    (hyA : y ∈ Set.range ψ) :
    (canonicalValuationStructure act A B₀ ψ x hx).restrict
        act A B₀ ψ y hy =
      canonicalValuationStructure act A B₀ ψ y hyA := by
  apply Subtype.ext
  funext z
  apply canonicalValuationFunction_proof_irrel act A B₀ ψ

section UnaryProjection

variable [L.HasUnaryFunctions]

/-- Projection of the faithful witness to the given base witness. -/
noncomputable def projection :
    Structure.Homomorphism act
      (witnessStructure act A B₀ ψ) B₀ where
  lang := 1
  toFun := WitnessVertex.base
  map_rel := by
    intro n R xs hrel
    simpa using hrel.1
  map_func := by
    intro n F xs
    have hxs :
        xs = fun _ => xs (UnaryFunctions.unaryIndex F) :=
      UnaryFunctions.unaryTuple_eq_constant F xs
    rw [hxs]
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    change
      z ∈
        (witnessStructure act A B₀ ψ).func F
          (fun _ => xs (UnaryFunctions.unaryIndex F)) at hz
    rcases hz with ⟨b, hb, rfl⟩
    simpa using hb

/-- Projection is literally the first coordinate. -/
@[simp] theorem projection_apply
    (w : WitnessVertex act A B₀ ψ) :
    projection act A B₀ ψ w = w.base :=
  rfl

end UnaryProjection

/-- Every family of canonical witness vertices is generic. -/
theorem canonicalFamilyGeneric
    {ι : Type*} (as : ι → α) :
    WitnessFamilyGeneric act A B₀ ψ
      (fun i => canonicalVertex act A B₀ ψ (as i)) := by
  intro i j y z
  let hri :
      y.1 ∈ Set.range ψ :=
    closureAtSet_subset_embedding_range act A B₀ ψ
      (show ψ (as i) ∈ Set.range ψ from ⟨as i, rfl⟩) y.2
  let hrj :
      z.1 ∈ Set.range ψ :=
    closureAtSet_subset_embedding_range act A B₀ ψ
      (show ψ (as j) ∈ Set.range ψ from ⟨as j, rfl⟩) z.2
  simpa [WitnessVertex.pointAt, valuationPointAt,
    WitnessVertex.valuation, canonicalVertex,
    canonicalValuationStructure] using
    (canonical_areGeneric act A B₀ ψ hri hrj)

end Faithful
end AllThoseEPPA
