import AllThoseEPPA.Irreducible

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

end Faithful
end AllThoseEPPA
