import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fin.Tuple.Basic
import AllThoseEPPA.RelationalWitness
import AllThoseEPPA.FiniteSet
import AllThoseEPPA.F2Completion

/-!
# Extending partial automorphisms in the relational valuation witness

This file starts the extension construction from Section `sec:relstructures`.

The paper writes the flip data as maps
`F_R : A^n → {0,1}^n`.  We use the additive structure on `Bool`;
under `Mathlib.Algebra.Ring.BooleanRing`, addition is XOR, so this is
literally the two-element field/additive group viewpoint suggested by the
construction.

The first checkpoint isolates the affine correction forced on coordinates
already in the source of a partial automorphism.
-/

namespace AllThoseEPPA
namespace Relational

universe u v w

variable {L : Language.{u}} [L.IsRelational]
variable {Γ : Type w} [Group Γ]
variable (act : L.Action Γ)
variable {α : Type v} [Fintype α] [LinearOrder α]
variable (A : Structure L α)

/-- Partial automorphisms of the input relational structure. -/
abbrev RelPartialAutomorphism :=
  Structure.PartialAutomorphism act A

/-- The coherent order-preserving extension of the underlying partial
permutation of vertices. -/
noncomputable def baseExtension
    (p : RelPartialAutomorphism act A) : Equiv.Perm α :=
  PartialEquiv.orderedExtension p.toPartialEquiv

@[simp] theorem baseExtension_apply_of_mem
    (p : RelPartialAutomorphism act A) {x : α}
    (hx : x ∈ p.source) :
    baseExtension act A p x = p x :=
  PartialEquiv.orderedExtension_apply_of_mem p.toPartialEquiv hx

/-- A partial automorphism preserves every relation on tuples from its source,
with the relation symbol relabelled by its language component. -/
theorem partialAutomorphism_rel_iff
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α)
    (hxs : ∀ i, xs i ∈ p.source) :
    A.rel (act.onRel p.lang R) (p.toPartialEquiv ∘ xs) ↔
      A.rel R xs :=
  p.map_rel_iff R xs hxs

/-- The affine correction prescribed by a source vertex `x` for an
`R`-tuple `xs`.

In additive notation this is
`χ_x(R,xs) + χ_{p x}(pR, hat p xs)` in `𝔽₂`. -/
noncomputable def sourceCorrection
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α) (x : α) : Bool := by
  classical
  if hx : x ∈ p.source then
    exact
      genericValuation A x ⟨n, R⟩ xs +
        genericValuation A (p x)
          ⟨n, act.onRel p.lang R⟩
          (baseExtension act A p ∘ xs)
  else
    exact false

@[simp] theorem sourceCorrection_of_not_mem
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α) {x : α}
    (hx : x ∉ p.source) :
    sourceCorrection act A p R xs x = false := by
  classical
  simp [sourceCorrection, hx]

/-- On a source vertex the correction is exactly the difference of the old and
new generic valuation entries. -/
theorem sourceCorrection_of_mem
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α) {x : α}
    (hx : x ∈ p.source) :
    sourceCorrection act A p R xs x =
      genericValuation A x ⟨n, R⟩ xs +
        genericValuation A (p x)
          ⟨n, act.onRel p.lang R⟩
          (baseExtension act A p ∘ xs) := by
  classical
  simp [sourceCorrection, hx]

/-- The generic valuation at `x` can only see tuples whose first coordinate
is `x`.  Consequently the source part of the paper's flip matrix is zero
away from the base of the first coordinate. -/
theorem sourceCorrection_eq_false_of_ne_first
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α) {x : α}
    (hxfirst : x ≠ xs (Language.firstIndex R)) :
    sourceCorrection act A p R xs x = false := by
  classical
  by_cases hx : x ∈ p.source
  · rw [sourceCorrection_of_mem act A p R xs hx]
    have hold :
        genericValuation A x ⟨n, R⟩ xs = false := by
      simp [genericValuation, hxfirst]
    have hnew :
        genericValuation A (p x)
          ⟨n, act.onRel p.lang R⟩
          (baseExtension act A p ∘ xs) = false := by
      unfold genericValuation
      apply Bool.decide_false
      rintro ⟨_, hp⟩
      have hp' :
          p x =
            baseExtension act A p (xs (Language.firstIndex R)) := by
        simpa [Function.comp_apply] using hp
      have hσx :
          baseExtension act A p x =
            baseExtension act A p (xs (Language.firstIndex R)) := by
        rw [baseExtension_apply_of_mem act A p hx]
        exact hp'
      exact hxfirst ((baseExtension act A p).injective hσx)
    rw [hold, hnew]
    exact Bool.zero_eq_false
  · exact sourceCorrection_of_not_mem act A p R xs hx

/-- Sum in `𝔽₂` of the case-(1) corrections over distinct source vertices.
This is the forced vector fed into the generic parity-completion operator. -/
noncomputable def sourceParity
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α) : Bool :=
  F2Completion.sourceParity p.source xs
    (sourceCorrection act A p R xs)

/-- If the first base is not in the source, every case-(1) correction is zero. -/
theorem sourceParity_eq_false_of_first_not_mem
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α)
    (hfirst : xs (Language.firstIndex R) ∉ p.source) :
    sourceParity act A p R xs = false := by
  classical
  unfold sourceParity F2Completion.sourceParity
  apply Finset.sum_eq_zero
  intro i hi
  have hi' :
      xs i ∈ p.source := by
    exact (Finset.mem_filter.mp
      (show i ∈ F2Completion.sourceRepresentatives p.source xs from hi)).2
  by_cases hbase : xs i = xs (Language.firstIndex R)
  · exact (hfirst (hbase ▸ hi')).elim
  · exact sourceCorrection_eq_false_of_ne_first act A p R xs hbase

end Relational
end AllThoseEPPA
