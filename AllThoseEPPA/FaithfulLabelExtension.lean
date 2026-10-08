import AllThoseEPPA.FaithfulLabelFibres

/-!
# Canonical total extensions of faithful label bijections
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w z u₁ u₂

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)

/-- Package an equivalence between subtypes as a partial equivalence of the
ambient types.  A full fallback equivalence supplies irrelevant values outside
the source and target. -/
noncomputable def partialEquivOfSubtypeEquiv
    {X : Type u₁} {Y : Type u₂}
    (S : Set X) (T : Set Y)
    (e : S ≃ T) (fallback : X ≃ Y) :
    PartialEquiv X Y := by
  classical
  refine
    { toFun := fun x =>
        if hx : x ∈ S then (e ⟨x, hx⟩).1 else fallback x
      invFun := fun y =>
        if hy : y ∈ T then (e.symm ⟨y, hy⟩).1 else fallback.symm y
      source := S
      target := T
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_ }
  · intro x hx
    simp [hx]
  · intro y hy
    simp [hy]
  · intro x hx
    have heT : (e ⟨x, hx⟩).1 ∈ T := (e ⟨x, hx⟩).2
    simp [hx, heT]
  · intro y hy
    have heS : (e.symm ⟨y, hy⟩).1 ∈ S :=
      (e.symm ⟨y, hy⟩).2
    simp [hy, heS]

@[simp] theorem partialEquivOfSubtypeEquiv_source
    {X : Type u₁} {Y : Type u₂}
    (S : Set X) (T : Set Y)
    (e : S ≃ T) (fallback : X ≃ Y) :
    (partialEquivOfSubtypeEquiv S T e fallback).source = S :=
  rfl

@[simp] theorem partialEquivOfSubtypeEquiv_target
    {X : Type u₁} {Y : Type u₂}
    (S : Set X) (T : Set Y)
    (e : S ≃ T) (fallback : X ≃ Y) :
    (partialEquivOfSubtypeEquiv S T e fallback).target = T :=
  rfl

theorem partialEquivOfSubtypeEquiv_apply_of_mem
    {X : Type u₁} {Y : Type u₂}
    (S : Set X) (T : Set Y)
    (e : S ≃ T) (fallback : X ≃ Y)
    {x : X} (hx : x ∈ S) :
    partialEquivOfSubtypeEquiv S T e fallback x =
      (e ⟨x, hx⟩).1 := by
  classical
  simp [partialEquivOfSubtypeEquiv, hx]

/-- An arbitrary full equivalence between the label types of `I` and
`g(I)`; it is used only outside the source of the prescribed partial label
bijection. -/
noncomputable def labelFallbackEquiv [Finite β]
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ) :
    BadLabel act A B₀ ψ I ≃
      BadLabel act A B₀ ψ
        (I.transport act A B₀ ψ g) := by
  letI : Fintype (BadLabel act A B₀ ψ I) :=
    badLabelFintype act A B₀ ψ I
  letI :
      Fintype
        (BadLabel act A B₀ ψ
          (I.transport act A B₀ ψ g)) :=
    badLabelFintype act A B₀ ψ
      (I.transport act A B₀ ψ g)
  exact
    Fintype.equivOfCardEq
      ((by
        simpa only [Nat.card_eq_fintype_card] using
          (badLabel_transport_card act A B₀ ψ g I)))

/-- The paper's partial permutation `τ_I^φ`, with heterogeneous source and
target label types. -/
noncomputable def labelPartialEquiv [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g) :
    PartialEquiv
      (BadLabel act A B₀ ψ I)
      (BadLabel act A B₀ ψ
        (I.transport act A B₀ ψ g)) :=
  partialEquivOfSubtypeEquiv
    (usedSourceLabels act A B₀ ψ p I)
    (usedTargetLabels act A B₀ ψ p g I)
    (usedLabelEquiv act A B₀ ψ p g I
      hsource htarget hcompat)
    (labelFallbackEquiv act A B₀ ψ g I)

@[simp] theorem labelPartialEquiv_source [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g) :
    (labelPartialEquiv act A B₀ ψ p g I
      hsource htarget hcompat).source =
      usedSourceLabels act A B₀ ψ p I :=
  rfl

@[simp] theorem labelPartialEquiv_target [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g) :
    (labelPartialEquiv act A B₀ ψ p g I
      hsource htarget hcompat).target =
      usedTargetLabels act A B₀ ψ p g I :=
  rfl

/-- Canonical total extension `\hat τ_I^φ`. -/
noncomputable def labelExtension [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g) :
    BadLabel act A B₀ ψ I ≃
      BadLabel act A B₀ ψ
        (I.transport act A B₀ ψ g) := by
  letI : Fintype (BadLabel act A B₀ ψ I) :=
    badLabelFintype act A B₀ ψ I
  letI :
      Fintype
        (BadLabel act A B₀ ψ
          (I.transport act A B₀ ψ g)) :=
    badLabelFintype act A B₀ ψ
      (I.transport act A B₀ ψ g)
  letI : LinearOrder (BadLabel act A B₀ ψ I) :=
    badLabelLinearOrder act A B₀ ψ I
  letI :
      LinearOrder
        (BadLabel act A B₀ ψ
          (I.transport act A B₀ ψ g)) :=
    badLabelLinearOrder act A B₀ ψ
      (I.transport act A B₀ ψ g)
  exact
    PartialEquiv.orderedExtensionOfCardEq
      (labelPartialEquiv act A B₀ ψ p g I
        hsource htarget hcompat)
      ((by
        simpa only [Nat.card_eq_fintype_card] using
          (badLabel_transport_card act A B₀ ψ g I)))

/-- The total label extension agrees with the prescribed used-label
bijection. -/
theorem labelExtension_apply_of_used [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    {l : BadLabel act A B₀ ψ I}
    (hl : l ∈ usedSourceLabels act A B₀ ψ p I) :
    labelExtension act A B₀ ψ p g I
        hsource htarget hcompat l =
      (usedLabelEquiv act A B₀ ψ p g I
        hsource htarget hcompat ⟨l, hl⟩).1 := by
  letI : Fintype (BadLabel act A B₀ ψ I) :=
    badLabelFintype act A B₀ ψ I
  letI :
      Fintype
        (BadLabel act A B₀ ψ
          (I.transport act A B₀ ψ g)) :=
    badLabelFintype act A B₀ ψ
      (I.transport act A B₀ ψ g)
  letI : LinearOrder (BadLabel act A B₀ ψ I) :=
    badLabelLinearOrder act A B₀ ψ I
  letI :
      LinearOrder
        (BadLabel act A B₀ ψ
          (I.transport act A B₀ ψ g)) :=
    badLabelLinearOrder act A B₀ ψ
      (I.transport act A B₀ ψ g)
  rw [show
    labelExtension act A B₀ ψ p g I
        hsource htarget hcompat l =
      labelPartialEquiv act A B₀ ψ p g I
        hsource htarget hcompat l by
    exact
      PartialEquiv.orderedExtensionOfCardEq_apply_of_mem
        (labelPartialEquiv act A B₀ ψ p g I
          hsource htarget hcompat)
        ((by
        simpa only [Nat.card_eq_fintype_card] using
          (badLabel_transport_card act A B₀ ψ g I)))
        hl]
  exact
    partialEquivOfSubtypeEquiv_apply_of_mem
      (usedSourceLabels act A B₀ ψ p I)
      (usedTargetLabels act A B₀ ψ p g I)
      (usedLabelEquiv act A B₀ ψ p g I
        hsource htarget hcompat)
      (labelFallbackEquiv act A B₀ ψ g I)
      hl


/-- On a source witness vertex, the prescribed used-label bijection sends its
centre label to the centre label of its partial-automorphism image. -/
theorem usedLabelEquiv_centerLabel [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (w : WitnessVertex act A B₀ ψ)
    (hw : w ∈ p.source)
    (hwI : w.base ∈ I.carrier) :
    let htI :
        (p w).base ∈
          (I.transport act A B₀ ψ g).carrier :=
      ⟨w.base, hwI, hcompat.2 w hw⟩
    let hused :
        centerLabel act A B₀ ψ w I hwI ∈
          usedSourceLabels act A B₀ ψ p I :=
      ⟨⟨w, hw, hwI⟩, rfl⟩
    (usedLabelEquiv act A B₀ ψ p g I
        hsource htarget hcompat
        ⟨centerLabel act A B₀ ψ w I hwI, hused⟩).1 =
      centerLabel act A B₀ ψ (p w)
        (I.transport act A B₀ ψ g) htI := by
  dsimp
  let sw : SourceWitness act A B₀ ψ p I :=
    ⟨w, hw, hwI⟩
  have hs :
      sourceWitnessLabelEquiv act A B₀ ψ p I hsource sw =
        ⟨centerLabel act A B₀ ψ w I hwI,
          ⟨sw, rfl⟩⟩ := by
    apply Subtype.ext
    rfl
  rw [← hs]
  simp [usedLabelEquiv, sw, sourceTargetWitnessEquiv,
    targetWitnessLabelEquiv, targetLabelMap]
  apply Subtype.ext
  rfl

/-- Consequently the canonical total label extension agrees with the partial
witness automorphism on every centre label occurring in the source. -/
theorem labelExtension_centerLabel [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (w : WitnessVertex act A B₀ ψ)
    (hw : w ∈ p.source)
    (hwI : w.base ∈ I.carrier) :
    let htI :
        (p w).base ∈
          (I.transport act A B₀ ψ g).carrier :=
      ⟨w.base, hwI, hcompat.2 w hw⟩
    labelExtension act A B₀ ψ p g I
        hsource htarget hcompat
        (centerLabel act A B₀ ψ w I hwI) =
      centerLabel act A B₀ ψ (p w)
        (I.transport act A B₀ ψ g) htI := by
  dsimp
  let hused :
      centerLabel act A B₀ ψ w I hwI ∈
        usedSourceLabels act A B₀ ψ p I :=
    ⟨⟨w, hw, hwI⟩, rfl⟩
  rw [labelExtension_apply_of_used
    act A B₀ ψ p g I hsource htarget hcompat hused]
  exact
    usedLabelEquiv_centerLabel
      act A B₀ ψ p g I hsource htarget hcompat
      w hw hwI

end Faithful
end AllThoseEPPA
