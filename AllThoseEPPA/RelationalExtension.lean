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
      apply Bool.eq_false_of_not_eq_true
      intro hv
      have hv' :=
        (genericValuation_eq_true_iff A (p x)
          ⟨n, act.onRel p.lang R⟩
          (baseExtension act A p ∘ xs)).1 hv
      have hp' :
          p x =
            baseExtension act A p (xs (Language.firstIndex R)) := by
        simpa [Function.comp_apply] using hv'.2
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

/-- If the first base lies in the source, the forced parity is just the
single correction bit on that base. -/
theorem sourceParity_eq_sourceCorrection_first_of_mem
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α)
    (hfirst : xs (Language.firstIndex R) ∈ p.source) :
    sourceParity act A p R xs =
      sourceCorrection act A p R xs (xs (Language.firstIndex R)) := by
  classical
  let i₀ : Fin n := Language.firstIndex R
  have hi₀rep : i₀ ∈ F2Completion.representatives xs := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro j hj
    have hj0 : j.val < i₀.val := hj
    change j.val < 0 at hj0
    exact (Nat.not_lt_zero _ hj0).elim
  have hi₀src :
      i₀ ∈ F2Completion.sourceRepresentatives p.source xs := by
    apply Finset.mem_filter.mpr
    exact ⟨hi₀rep, hfirst⟩
  unfold sourceParity F2Completion.sourceParity
  apply Finset.sum_eq_single i₀
  · intro j hj hji
    have hjrep : j ∈ F2Completion.representatives xs :=
      (Finset.mem_filter.mp hj).1
    have hbase : xs j ≠ xs i₀ := by
      intro hb
      exact hji (F2Completion.representatives_injOn xs hjrep hi₀rep hb)
    have hz :=
      sourceCorrection_eq_false_of_ne_first act A p R xs
        (by simpa [i₀] using hbase)
    simpa [Bool.zero_eq_false] using hz
  · intro hi
    exact (hi hi₀src).elim

/-- If every entry of the tuple belongs to the source, the forced correction
already has even parity. -/
theorem sourceParity_eq_false_of_forall_mem
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α)
    (hxs : ∀ i, xs i ∈ p.source) :
    sourceParity act A p R xs = false := by
  classical
  let i₀ : Fin n := Language.firstIndex R
  rw [sourceParity_eq_sourceCorrection_first_of_mem act A p R xs
    (hxs i₀)]
  rw [sourceCorrection_of_mem act A p R xs (hxs i₀)]
  have hσ :
      baseExtension act A p ∘ xs =
        p.toPartialEquiv ∘ xs := by
    funext i
    simp [Function.comp_apply, baseExtension_apply_of_mem act A p (hxs i)]
  have hrel := partialAutomorphism_rel_iff act A p R xs hxs
  have hfirstσ :
      p (xs i₀) = baseExtension act A p (xs i₀) := by
    symm
    exact baseExtension_apply_of_mem act A p (hxs i₀)
  simp [genericValuation, hσ, hrel, i₀, hfirstσ,
    Bool.zero_eq_false, Bool.add_eq_xor]

/-- The completed flip correction `F_R(xs)`, viewed as a function of the
base vertex rather than of a tuple index. Equal base vertices therefore get
the same bit definitionally. -/
noncomputable def flipCorrection
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α)
    (x : α) : Bool :=
  F2Completion.evenCompletion p.source xs
    (sourceCorrection act A p R xs) x

@[simp] theorem flipCorrection_of_mem
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α)
    {x : α} (hx : x ∈ p.source) :
    flipCorrection act A p R xs x =
      sourceCorrection act A p R xs x :=
  F2Completion.evenCompletion_of_mem p.source xs
    (sourceCorrection act A p R xs) hx

/-- The completed flip vector has even total parity on the distinct base
vertices of every tuple. -/
theorem flipCorrection_totalParity
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α) :
    F2Completion.totalParity xs (flipCorrection act A p R xs) = false := by
  classical
  unfold flipCorrection
  by_cases h : ∃ i, xs i ∉ p.source
  · exact F2Completion.totalParity_evenCompletion_of_exists_outside
      p.source xs (sourceCorrection act A p R xs) h
  · have hall : ∀ i, xs i ∈ p.source := by
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    rw [F2Completion.totalParity_evenCompletion_of_forall_mem
      p.source xs (sourceCorrection act A p R xs) hall]
    exact sourceParity_eq_false_of_forall_mem act A p R xs hall


/-- The completed correction is zero at a base vertex which does not occur in
the tuple.  This is the support property needed to transport valuation
functions. -/
theorem flipCorrection_eq_false_of_not_mem_range
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α) {x : α}
    (hx : x ∉ Set.range xs) :
    flipCorrection act A p R xs x = false := by
  classical
  unfold flipCorrection
  by_cases hxsrc : x ∈ p.source
  · rw [F2Completion.evenCompletion_of_mem
      p.source xs (sourceCorrection act A p R xs) hxsrc]
    apply sourceCorrection_eq_false_of_ne_first act A p R xs
    intro hfirst
    exact hx ⟨Language.firstIndex R, hfirst.symm⟩
  · by_cases hout : ∃ i, xs i ∉ p.source
    · rw [F2Completion.evenCompletion_of_not_mem
        p.source xs (sourceCorrection act A p R xs) hxsrc hout]
      have hne :
          x ≠ xs (F2Completion.firstOutsideIndex p.source xs hout) := by
        intro hEq
        exact hx ⟨F2Completion.firstOutsideIndex p.source xs hout, hEq.symm⟩
      simp [hne, Bool.zero_eq_false]
    · simp [F2Completion.evenCompletion, hxsrc, hout, Bool.zero_eq_false]



/-- Pull a relation symbol back through the language component of a partial
automorphism. -/
def preRel
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (S : L.RelSymbol n) : L.RelSymbol n :=
  act.onRel p.lang⁻¹ S

@[simp] theorem relabel_preRel
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (S : L.RelSymbol n) :
    act.onRel p.lang (preRel act A p S) = S := by
  unfold preRel
  rw [← Language.Action.onRel_mul]
  simp

/-- Pull a tuple back through the chosen total extension of the vertex map. -/
noncomputable def preTuple
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (zs : Fin n → α) : Fin n → α :=
  (baseExtension act A p).symm ∘ zs

@[simp] theorem baseExtension_preTuple
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (zs : Fin n → α) :
    baseExtension act A p ∘ preTuple act A p zs = zs := by
  funext i
  simp [preTuple, Function.comp_apply]

/-- Affine transport of one valuation vertex.

This is the paper's map
`(x,χ) ↦ (hat p(x), f_x(χ))`, written as pullback plus translation in the
Boolean vector space of valuations. -/
noncomputable def extendWitnessVertex
    (p : RelPartialAutomorphism act A)
    (v : WitnessVertex L α) : WitnessVertex L α := by
  classical
  let σ := baseExtension act A p
  refine
    { base := σ v.base
      valuation := fun S zs =>
        v.valuation ⟨S.1, preRel act A p S.2⟩ (preTuple act A p zs) +
          flipCorrection act A p (preRel act A p S.2)
            (preTuple act A p zs) v.base
      off_support_false := ?_ }
  intro S zs hmiss
  have hmissOld :
      ∀ i, preTuple act A p zs i ≠ v.base := by
    intro i hi
    apply hmiss i
    have hσ := congrArg σ hi
    simpa [σ, preTuple, Function.comp_apply] using hσ
  have hval :
      v.valuation ⟨S.1, preRel act A p S.2⟩
          (preTuple act A p zs) = false :=
    v.off_support_false
      ⟨S.1, preRel act A p S.2⟩
      (preTuple act A p zs) hmissOld
  have hnrange :
      v.base ∉ Set.range (preTuple act A p zs) := by
    rintro ⟨i, hi⟩
    exact hmissOld i hi
  have hflip :
      flipCorrection act A p (preRel act A p S.2)
          (preTuple act A p zs) v.base = false :=
    flipCorrection_eq_false_of_not_mem_range
      act A p (preRel act A p S.2) (preTuple act A p zs) hnrange
  rw [hval, hflip]
  rfl

@[simp] theorem extendWitnessVertex_base
    (p : RelPartialAutomorphism act A)
    (v : WitnessVertex L α) :
    (extendWitnessVertex act A p v).base =
      baseExtension act A p v.base :=
  rfl

/-- On the generic copy and on the source of the partial automorphism, the
affine valuation transport agrees with the given partial automorphism. -/
theorem extendWitnessVertex_generic_of_mem
    (p : RelPartialAutomorphism act A)
    {x : α} (hx : x ∈ p.source) :
    extendWitnessVertex act A p (genericVertex A x) =
      genericVertex A (p x) := by
  classical
  apply WitnessVertex.ext
  · exact baseExtension_apply_of_mem act A p hx
  · funext S zs
    let R : L.RelSymbol S.1 := preRel act A p S.2
    let ys : Fin S.1 → α := preTuple act A p zs
    have hR : act.onRel p.lang R = S.2 := by
      simpa [R] using relabel_preRel act A p S.2
    have htuple :
        baseExtension act A p ∘ ys = zs := by
      simpa [ys] using baseExtension_preTuple act A p zs
    change
      genericValuation A x ⟨S.1, R⟩ ys +
          flipCorrection act A p R ys x =
        genericValuation A (p x) S zs
    rw [flipCorrection_of_mem act A p R ys hx]
    rw [sourceCorrection_of_mem act A p R ys hx]
    rw [hR, htuple]
    cases h₁ : genericValuation A x ⟨S.1, R⟩ ys <;>
      cases h₂ : genericValuation A (p x) S zs <;> rfl

end Relational
end AllThoseEPPA
