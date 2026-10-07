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


/-- The chosen total base permutation respects composition of compatible
partial automorphisms. -/
theorem baseExtension_comp
    (p q : RelPartialAutomorphism act A)
    (htg : p.target = q.source) :
    baseExtension act A (q.comp p htg) =
      (baseExtension act A p).trans (baseExtension act A q) := by
  exact PartialEquiv.orderedExtension_trans'
    p.toPartialEquiv q.toPartialEquiv htg

/-- The chosen total extension transports the source of the first partial
automorphism exactly onto the source of the second. -/
theorem baseExtension_mem_second_source_iff
    (p q : RelPartialAutomorphism act A)
    (htg : p.target = q.source) (x : α) :
    baseExtension act A p x ∈ q.source ↔ x ∈ p.source := by
  rw [← htg]
  exact PartialEquiv.orderedExtension_mem_target_iff p.toPartialEquiv x

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


/-- Forced affine corrections add under composition.  The second correction is
transported by the total extension of the first base map. -/
theorem sourceCorrection_comp_of_mem
    (p q : RelPartialAutomorphism act A)
    (htg : p.target = q.source)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α) {x : α}
    (hx : x ∈ p.source) :
    sourceCorrection act A (q.comp p htg) R xs x =
      sourceCorrection act A p R xs x +
        sourceCorrection act A q (act.onRel p.lang R)
          (baseExtension act A p ∘ xs) (baseExtension act A p x) := by
  classical
  have hqx :
      baseExtension act A p x ∈ q.source :=
    (baseExtension_mem_second_source_iff act A p q htg x).2 hx
  rw [sourceCorrection_of_mem act A (q.comp p htg) R xs hx]
  rw [sourceCorrection_of_mem act A p R xs hx]
  rw [sourceCorrection_of_mem act A q (act.onRel p.lang R)
    (baseExtension act A p ∘ xs) hqx]
  have hσx :
      baseExtension act A p x = p x :=
    baseExtension_apply_of_mem act A p hx
  rw [baseExtension_comp act A p q htg]
  simp only [Structure.PartialIsomorphism.comp, PartialEquiv.trans',
    Function.comp_apply]
  rw [Language.Action.onRel_mul]
  rw [hσx]
  have htuple :
      ((baseExtension act A p).trans (baseExtension act A q)) ∘ xs =
        baseExtension act A q ∘ (baseExtension act A p ∘ xs) := by
    rfl
  rw [htuple]
  let a := genericValuation A x ⟨n, R⟩ xs
  let b := genericValuation A (p x)
    ⟨n, act.onRel p.lang R⟩ (baseExtension act A p ∘ xs)
  let d := genericValuation A (q (p x))
    ⟨n, act.onRel q.lang (act.onRel p.lang R)⟩
    (baseExtension act A q ∘ (baseExtension act A p ∘ xs))
  change a + d = (a + b) + (b + d)
  cases a <;> cases b <;> cases d <;> rfl

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


/-- Completed flip corrections add under composition.  This is the central
affine coherence identity. -/
theorem flipCorrection_comp
    (p q : RelPartialAutomorphism act A)
    (htg : p.target = q.source)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α) (x : α) :
    flipCorrection act A (q.comp p htg) R xs x =
      flipCorrection act A p R xs x +
        flipCorrection act A q (act.onRel p.lang R)
          (baseExtension act A p ∘ xs) (baseExtension act A p x) := by
  classical
  change
    F2Completion.evenCompletion p.source xs
        (sourceCorrection act A (q.comp p htg) R xs) x =
      F2Completion.evenCompletion p.source xs
          (sourceCorrection act A p R xs) x +
        F2Completion.evenCompletion q.source
          (baseExtension act A p ∘ xs)
          (sourceCorrection act A q (act.onRel p.lang R)
            (baseExtension act A p ∘ xs))
          (baseExtension act A p x)
  have hDE :
      ∀ y, y ∈ p.source ↔ baseExtension act A p y ∈ q.source :=
    fun y => (baseExtension_mem_second_source_iff act A p q htg y).symm
  have hc :
      ∀ y, y ∈ p.source →
        sourceCorrection act A (q.comp p htg) R xs y =
          sourceCorrection act A p R xs y +
            sourceCorrection act A q (act.onRel p.lang R)
              (baseExtension act A p ∘ xs)
              (baseExtension act A p y) := by
    intro y hy
    exact sourceCorrection_comp_of_mem act A p q htg R xs hy
  calc
    _ =
        F2Completion.evenCompletion p.source xs
          (fun y =>
            sourceCorrection act A p R xs y +
              sourceCorrection act A q (act.onRel p.lang R)
                (baseExtension act A p ∘ xs)
                (baseExtension act A p y)) x := by
          exact F2Completion.evenCompletion_congr_source
            p.source xs
            (sourceCorrection act A (q.comp p htg) R xs)
            (fun y =>
              sourceCorrection act A p R xs y +
                sourceCorrection act A q (act.onRel p.lang R)
                  (baseExtension act A p ∘ xs)
                  (baseExtension act A p y))
            hc x
    _ =
        F2Completion.evenCompletion p.source xs
            (sourceCorrection act A p R xs) x +
          F2Completion.evenCompletion p.source xs
            (fun y =>
              sourceCorrection act A q (act.onRel p.lang R)
                (baseExtension act A p ∘ xs)
                (baseExtension act A p y)) x := by
          exact F2Completion.evenCompletion_add
            p.source xs
            (sourceCorrection act A p R xs)
            (fun y =>
              sourceCorrection act A q (act.onRel p.lang R)
                (baseExtension act A p ∘ xs)
                (baseExtension act A p y)) x
    _ = _ := by
      rw [← F2Completion.evenCompletion_equivariant
        (baseExtension act A p) p.source q.source hDE xs
        (sourceCorrection act A q (act.onRel p.lang R)
          (baseExtension act A p ∘ xs)) x]

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


@[simp] theorem preRel_relabel
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n) :
    preRel act A p (act.onRel p.lang R) = R := by
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


@[simp] theorem preTuple_baseExtension
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (xs : Fin n → α) :
    preTuple act A p (baseExtension act A p ∘ xs) = xs := by
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


/-- Coordinate formula for the affine transport. -/
theorem extendWitnessVertex_valuation_relabel
    (p : RelPartialAutomorphism act A)
    (v : WitnessVertex L α)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → α) :
    (extendWitnessVertex act A p v).valuation
        ⟨n, act.onRel p.lang R⟩
        (baseExtension act A p ∘ xs) =
      v.valuation ⟨n, R⟩ xs +
        flipCorrection act A p R xs v.base := by
  change
    v.valuation
        ⟨n, preRel act A p (act.onRel p.lang R)⟩
        (preTuple act A p (baseExtension act A p ∘ xs)) +
      flipCorrection act A p
        (preRel act A p (act.onRel p.lang R))
        (preTuple act A p (baseExtension act A p ∘ xs)) v.base =
      _
  rw [preRel_relabel, preTuple_baseExtension]

/-- Affine witness-vertex extensions respect composition. -/
theorem extendWitnessVertex_comp
    (p q : RelPartialAutomorphism act A)
    (htg : p.target = q.source)
    (v : WitnessVertex L α) :
    extendWitnessVertex act A (q.comp p htg) v =
      extendWitnessVertex act A q (extendWitnessVertex act A p v) := by
  classical
  apply WitnessVertex.ext
  · simp only [extendWitnessVertex_base]
    rw [baseExtension_comp act A p q htg]
    rfl
  · funext S zs
    rcases S with ⟨n, S⟩
    let r : RelPartialAutomorphism act A := q.comp p htg
    let R : L.RelSymbol n := preRel act A r S
    let xs : Fin n → α := preTuple act A r zs
    have hR : act.onRel r.lang R = S := by
      simpa [R] using relabel_preRel act A r S
    have hzs : baseExtension act A r ∘ xs = zs := by
      simpa [xs] using baseExtension_preTuple act A r zs
    have hLang :
        act.onRel r.lang R =
          act.onRel q.lang (act.onRel p.lang R) := by
      simp [r, Structure.PartialIsomorphism.comp,
        Language.Action.onRel_mul]
    have hBase :
        baseExtension act A r ∘ xs =
          baseExtension act A q ∘
            (baseExtension act A p ∘ xs) := by
      simp [r, baseExtension_comp, Function.comp_assoc]
    rw [← hR, ← hzs]
    rw [extendWitnessVertex_valuation_relabel act A r v R xs]
    rw [hLang, hBase]
    rw [extendWitnessVertex_valuation_relabel act A q
      (extendWitnessVertex act A p v)
      (act.onRel p.lang R) (baseExtension act A p ∘ xs)]
    rw [extendWitnessVertex_valuation_relabel act A p v R xs]
    rw [show r = q.comp p htg by rfl]
    rw [flipCorrection_comp act A p q htg R xs v.base]
    simp [add_assoc]

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



/-- Explicit inverse affine transport on witness vertices. -/
noncomputable def unextendWitnessVertex
    (p : RelPartialAutomorphism act A)
    (w : WitnessVertex L α) : WitnessVertex L α := by
  classical
  let σ := baseExtension act A p
  let x := σ.symm w.base
  refine
    { base := x
      valuation := fun R ys =>
        w.valuation ⟨R.1, act.onRel p.lang R.2⟩ (σ ∘ ys) +
          flipCorrection act A p R.2 ys x
      off_support_false := ?_ }
  intro R ys hmiss
  have hmissTarget :
      ∀ i, (σ ∘ ys) i ≠ w.base := by
    intro i hi
    apply hmiss i
    have hpre := congrArg σ.symm hi
    simpa [σ, x, Function.comp_apply] using hpre
  have hval :
      w.valuation ⟨R.1, act.onRel p.lang R.2⟩ (σ ∘ ys) = false :=
    w.off_support_false
      ⟨R.1, act.onRel p.lang R.2⟩ (σ ∘ ys) hmissTarget
  have hnrange : x ∉ Set.range ys := by
    rintro ⟨i, hi⟩
    exact hmiss i hi
  have hflip :
      flipCorrection act A p R.2 ys x = false :=
    flipCorrection_eq_false_of_not_mem_range
      act A p R.2 ys hnrange
  rw [hval, hflip]
  rfl

@[simp] theorem unextendWitnessVertex_base
    (p : RelPartialAutomorphism act A)
    (w : WitnessVertex L α) :
    (unextendWitnessVertex act A p w).base =
      (baseExtension act A p).symm w.base :=
  rfl

theorem unextendWitnessVertex_valuation
    (p : RelPartialAutomorphism act A)
    (w : WitnessVertex L α)
    (R : L.AnyRelSymbol) (ys : Fin R.1 → α) :
    (unextendWitnessVertex act A p w).valuation R ys =
      w.valuation ⟨R.1, act.onRel p.lang R.2⟩
          (baseExtension act A p ∘ ys) +
        flipCorrection act A p R.2 ys
          ((baseExtension act A p).symm w.base) :=
  rfl

theorem unextend_extend
    (p : RelPartialAutomorphism act A)
    (v : WitnessVertex L α) :
    unextendWitnessVertex act A p (extendWitnessVertex act A p v) = v := by
  classical
  apply WitnessVertex.ext
  · simp [unextendWitnessVertex]
  · funext R ys
    rw [unextendWitnessVertex_valuation]
    simp only [extendWitnessVertex_base, Equiv.symm_apply_apply]
    rw [extendWitnessVertex_valuation_relabel]
    cases hval : v.valuation R ys <;>
      cases hflip : flipCorrection act A p R.2 ys v.base <;> rfl

theorem extend_unextend
    (p : RelPartialAutomorphism act A)
    (w : WitnessVertex L α) :
    extendWitnessVertex act A p (unextendWitnessVertex act A p w) = w := by
  classical
  apply WitnessVertex.ext
  · simp [extendWitnessVertex, unextendWitnessVertex]
  · funext S zs
    let R : L.RelSymbol S.1 := preRel act A p S.2
    let ys : Fin S.1 → α := preTuple act A p zs
    change
      (w.valuation ⟨S.1, act.onRel p.lang R⟩
          (baseExtension act A p ∘ ys) +
        flipCorrection act A p R ys
          ((baseExtension act A p).symm w.base)) +
        flipCorrection act A p R ys
          ((baseExtension act A p).symm w.base) =
      w.valuation S zs
    rw [show act.onRel p.lang R = S.2 by
      simpa [R] using relabel_preRel act A p S.2]
    rw [show baseExtension act A p ∘ ys = zs by
      simpa [ys] using baseExtension_preTuple act A p zs]
    cases hval : w.valuation S zs <;>
      cases hflip :
        flipCorrection act A p R ys
          ((baseExtension act A p).symm w.base) <;> rfl

/-- The affine transport is a permutation of all relational witness vertices. -/
noncomputable def witnessVertexEquiv
    (p : RelPartialAutomorphism act A) :
    WitnessVertex L α ≃ WitnessVertex L α where
  toFun := extendWitnessVertex act A p
  invFun := unextendWitnessVertex act A p
  left_inv := unextend_extend act A p
  right_inv := extend_unextend act A p

@[simp] theorem witnessVertexEquiv_apply
    (p : RelPartialAutomorphism act A)
    (v : WitnessVertex L α) :
    witnessVertexEquiv act A p v = extendWitnessVertex act A p v :=
  rfl



/-- XOR of the valuation bits contributed by the distinct base vertices of a
witness tuple. -/
noncomputable def tupleValuationParity
    {n : ℕ} (R : L.RelSymbol n)
    (vs : Fin n → WitnessVertex L α) : Bool := by
  classical
  exact ∑ i ∈ F2Completion.representatives (WitnessVertex.bases vs),
    (vs i).valuation ⟨n, R⟩ (WitnessVertex.bases vs)

/-- The paper's active indices are exactly the first-occurrence
representatives whose valuation bit is one. -/
theorem activeIndices_eq_filter_representatives
    {n : ℕ} (R : L.RelSymbol n)
    (vs : Fin n → WitnessVertex L α) :
    WitnessVertex.activeIndices R vs =
      (F2Completion.representatives (WitnessVertex.bases vs)).filter
        (fun i =>
          (vs i).valuation ⟨n, R⟩ (WitnessVertex.bases vs) = true) := by
  classical
  ext i
  constructor
  · intro hi
    have hi' := Finset.mem_filter.mp hi
    rcases hi'.2 with ⟨hfirst, hval⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [WitnessVertex.IsFirstBase, F2Completion.IsFirstValue,
        WitnessVertex.bases] using hfirst
    · exact hval
  · intro hi
    have hi' := Finset.mem_filter.mp hi
    have hrep := Finset.mem_filter.mp hi'.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, hi'.2⟩
    simpa [WitnessVertex.IsFirstBase, F2Completion.IsFirstValue,
      WitnessVertex.bases] using hrep.2

/-- Linear form of the witness relation: compatibility plus XOR-parity one. -/
theorem relationHolds_iff_tupleValuationParity
    {n : ℕ} (R : L.RelSymbol n)
    (vs : Fin n → WitnessVertex L α) :
    WitnessVertex.RelationHolds R vs ↔
      WitnessVertex.TupleCompatible vs ∧
        tupleValuationParity R vs = true := by
  classical
  change
    (WitnessVertex.TupleCompatible vs ∧
      (WitnessVertex.activeIndices R vs).card % 2 = 1) ↔
    (WitnessVertex.TupleCompatible vs ∧
      tupleValuationParity R vs = true)
  constructor
  · rintro ⟨hcompat, hodd⟩
    refine ⟨hcompat, ?_⟩
    unfold tupleValuationParity
    apply (F2Completion.sum_bool_eq_true_iff_filter_card_mod_two
      (F2Completion.representatives (WitnessVertex.bases vs))
      (fun i =>
        (vs i).valuation ⟨n, R⟩ (WitnessVertex.bases vs))).2
    rw [← activeIndices_eq_filter_representatives R vs]
    exact hodd
  · rintro ⟨hcompat, hsum⟩
    refine ⟨hcompat, ?_⟩
    have hodd :=
      (F2Completion.sum_bool_eq_true_iff_filter_card_mod_two
        (F2Completion.representatives (WitnessVertex.bases vs))
        (fun i =>
          (vs i).valuation ⟨n, R⟩ (WitnessVertex.bases vs))).1
        (by simpa [tupleValuationParity] using hsum)
    rw [← activeIndices_eq_filter_representatives R vs] at hodd
    exact hodd

@[simp] theorem bases_extendWitnessVertex
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (vs : Fin n → WitnessVertex L α) :
    WitnessVertex.bases (extendWitnessVertex act A p ∘ vs) =
      baseExtension act A p ∘ WitnessVertex.bases vs := by
  funext i
  rfl

/-- Tuple compatibility is preserved and reflected by the affine witness
permutation. -/
theorem tupleCompatible_extend_iff
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (vs : Fin n → WitnessVertex L α) :
    WitnessVertex.TupleCompatible (extendWitnessVertex act A p ∘ vs) ↔
      WitnessVertex.TupleCompatible vs := by
  constructor
  · intro h i j hij
    have hijTarget :
        ((extendWitnessVertex act A p ∘ vs) i).base =
          ((extendWitnessVertex act A p ∘ vs) j).base := by
      change
        baseExtension act A p (vs i).base =
          baseExtension act A p (vs j).base
      exact congrArg (baseExtension act A p) hij
    have hext := h i j hijTarget
    exact (witnessVertexEquiv act A p).injective
      (by simpa [Function.comp_apply] using hext)
  · intro h i j hij
    have hijBase : (vs i).base = (vs j).base := by
      apply (baseExtension act A p).injective
      simpa [Function.comp_apply] using hij
    have hv := h i j hijBase
    simpa [Function.comp_apply] using
      congrArg (extendWitnessVertex act A p) hv

/-- The XOR valuation sum is invariant under the affine witness
transformation. -/
theorem tupleValuationParity_extend
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n)
    (vs : Fin n → WitnessVertex L α) :
    tupleValuationParity (act.onRel p.lang R)
        (extendWitnessVertex act A p ∘ vs) =
      tupleValuationParity R vs := by
  classical
  unfold tupleValuationParity
  rw [bases_extendWitnessVertex]
  rw [F2Completion.representatives_comp_injective
    (baseExtension act A p) (baseExtension act A p).injective
    (WitnessVertex.bases vs)]
  simp_rw [Function.comp_apply]
  simp_rw [extendWitnessVertex_valuation_relabel act A p]
  rw [Finset.sum_add_distrib]
  have hflip :=
    flipCorrection_totalParity act A p R (WitnessVertex.bases vs)
  unfold F2Completion.totalParity at hflip
  have hflip' :
      (∑ i ∈ F2Completion.representatives (WitnessVertex.bases vs),
        flipCorrection act A p R (WitnessVertex.bases vs) (vs i).base) =
        false := by
    simpa [WitnessVertex.bases] using hflip
  rw [hflip']
  simp [Bool.zero_eq_false]

/-- Every relation of the valuation witness is preserved and reflected by the
affine extension, with the relation symbol relabelled by `p.lang`. -/
theorem witnessRelation_extend_iff
    (p : RelPartialAutomorphism act A)
    {n : ℕ} (R : L.RelSymbol n)
    (vs : Fin n → WitnessVertex L α) :
    (witnessStructure (L := L) α).rel (act.onRel p.lang R)
        (extendWitnessVertex act A p ∘ vs) ↔
      (witnessStructure (L := L) α).rel R vs := by
  change
    WitnessVertex.RelationHolds (act.onRel p.lang R)
        (extendWitnessVertex act A p ∘ vs) ↔
      WitnessVertex.RelationHolds R vs
  rw [relationHolds_iff_tupleValuationParity,
    relationHolds_iff_tupleValuationParity]
  rw [tupleCompatible_extend_iff, tupleValuationParity_extend]



/-- The affine witness-vertex permutation as an automorphism in the common
`Γ_L`-structure API. -/
noncomputable def witnessAutomorphism
    (p : RelPartialAutomorphism act A) :
    Structure.Automorphism act (witnessStructure (L := L) α) where
  toPartialIsomorphism :=
    { lang := p.lang
      toPartialEquiv := (witnessVertexEquiv act A p).toPartialEquiv
      source_closed :=
        Structure.isClosed_univ (witnessStructure (L := L) α)
      target_closed :=
        Structure.isClosed_univ (witnessStructure (L := L) α)
      map_rel_iff := by
        intro n R vs hvs
        change
          (witnessStructure (L := L) α).rel (act.onRel p.lang R)
              (extendWitnessVertex act A p ∘ vs) ↔
            (witnessStructure (L := L) α).rel R vs
        exact witnessRelation_extend_iff act A p R vs
      map_func := by
        intro n F vs hvs
        exact isEmptyElim F }
  source_eq_univ := rfl
  target_eq_univ := rfl

/-- The affine witness automorphism extends the original partial automorphism
along the generic copy. -/
theorem witnessAutomorphism_extends
    (p : RelPartialAutomorphism act A) :
    Structure.ExtendsAlong act (genericEmbedding act A) p
      (witnessAutomorphism act A p) := by
  constructor
  · change p.lang * 1 = 1 * p.lang
    simp
  · intro x hx
    change
      extendWitnessVertex act A p (genericVertex A x) =
        genericVertex A (p x)
    exact extendWitnessVertex_generic_of_mem act A p hx

/-- The finite relational valuation witness is a plain EPPA-witness. -/
theorem relationalWitness_isEPPAWitness :
    Structure.IsEPPAWitness act (genericEmbedding act A) := by
  intro p
  exact ⟨witnessAutomorphism act A p,
    witnessAutomorphism_extends act A p⟩

/-- **Finite relational structures have EPPA (affine valuation witness).**

This is the plain-EPPA part of Proposition `prop:relstructures`.  The
coherence of the simultaneous extension map is formalized separately. -/
theorem finiteRelationalStructuresHaveEPPA
    {β : Type v} [Fintype β] [Finite L.AnyRelSymbol]
    (B : Structure L β) :
    ∃ ψ : Structure.Embedding act B
        (witnessStructure (L := L) β),
      Structure.IsEPPAWitness act ψ := by
  classical
  letI : LinearOrder β :=
    LinearOrder.lift' (Fintype.equivFin β) (Fintype.equivFin β).injective
  exact ⟨genericEmbedding act B,
    relationalWitness_isEPPAWitness act B⟩

end Relational
end AllThoseEPPA
