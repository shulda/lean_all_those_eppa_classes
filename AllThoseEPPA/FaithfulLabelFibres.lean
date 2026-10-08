import AllThoseEPPA.FaithfulLabels

/-!
# Label fibres for faithful partial automorphisms

This file isolates the finite partial bijection on labels attached to a
partial automorphism of the faithful witness and a compatible automorphism of
the base witness.
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)

/-- The valuation point of a witness vertex at its own base point. -/
def centerPoint
    (w : WitnessVertex act A B₀ ψ) :
    B₀.closureAtSet w.base :=
  ⟨w.base, B₀.mem_closureAtSet w.base⟩

def centerValuationPoint
    (w : WitnessVertex act A B₀ ψ) :
    ValuationPoint act A B₀ ψ :=
  w.pointAt act A B₀ ψ (centerPoint act A B₀ ψ w)

/-- The label carried at the centre of a witness vertex for a bad
irreducible containing its base point. -/
def centerLabel
    (w : WitnessVertex act A B₀ ψ)
    (I : BadIrreducible act A B₀ ψ)
    (hwI : w.base ∈ I.carrier) :
    BadLabel act A B₀ ψ I :=
  (centerValuationPoint act A B₀ ψ w).2 ⟨I, hwI⟩

/-- A base automorphism is compatible with a partial witness automorphism when
it has the same language component and extends its projection on the source. -/
def BaseCompatible
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀) : Prop :=
  g.lang = p.lang ∧
    ∀ x, x ∈ p.source → g x.base = (p x).base

/-- Source witnesses whose base lies in a fixed bad irreducible. -/
abbrev SourceWitness
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (I : BadIrreducible act A B₀ ψ) :=
  {x : WitnessVertex act A B₀ ψ //
    x ∈ p.source ∧ x.base ∈ I.carrier}

/-- Target witnesses whose base lies in the transported bad irreducible. -/
abbrev TargetWitness
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ) :=
  {x : WitnessVertex act A B₀ ψ //
    x ∈ p.target ∧
      x.base ∈ (I.transport act A B₀ ψ g).carrier}

def sourceLabelMap
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (I : BadIrreducible act A B₀ ψ) :
    SourceWitness act A B₀ ψ p I →
      BadLabel act A B₀ ψ I :=
  fun x => centerLabel act A B₀ ψ x.1 I x.2.2

noncomputable def targetLabelMap
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ) :
    TargetWitness act A B₀ ψ p g I →
      BadLabel act A B₀ ψ
        (I.transport act A B₀ ψ g) :=
  fun x =>
    centerLabel act A B₀ ψ x.1
      (I.transport act A B₀ ψ g) x.2.2

theorem sourceLabelMap_injective
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (I : BadIrreducible act A B₀ ψ)
    (hgen : WitnessSetGeneric act A B₀ ψ p.source) :
    Function.Injective
      (sourceLabelMap act A B₀ ψ p I) := by
  intro x y hlabel
  have hg :=
    hgen
      ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩
      (centerPoint act A B₀ ψ x.1)
      (centerPoint act A B₀ ψ y.1)
  rcases hg with heq | ⟨hbase, hlabels⟩
  · apply Subtype.ext
    exact
      projection_injOn_of_generic
        act A B₀ ψ p.source hgen
        x.2.1 y.2.1
        (congrArg
          (fun q : ValuationPoint act A B₀ ψ => q.1) heq)
  · exfalso
    apply hlabels I x.2.2 y.2.2
    exact congrArg Subtype.val hlabel

theorem targetLabelMap_injective
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hgen : WitnessSetGeneric act A B₀ ψ p.target) :
    Function.Injective
      (targetLabelMap act A B₀ ψ p g I) := by
  intro x y hlabel
  have hg :=
    hgen
      ⟨x.1, x.2.1⟩
      ⟨y.1, y.2.1⟩
      (centerPoint act A B₀ ψ x.1)
      (centerPoint act A B₀ ψ y.1)
  rcases hg with heq | ⟨hbase, hlabels⟩
  · apply Subtype.ext
    exact
      projection_injOn_of_generic
        act A B₀ ψ p.target hgen
        x.2.1 y.2.1
        (congrArg
          (fun q : ValuationPoint act A B₀ ψ => q.1) heq)
  · exfalso
    apply hlabels
      (I.transport act A B₀ ψ g)
      x.2.2 y.2.2
    exact congrArg Subtype.val hlabel

/-- A compatible base automorphism transports the witness fibre over `I`
bijectively to the target witness fibre over `g(I)`. -/
noncomputable def sourceTargetWitnessEquiv
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hcompat : BaseCompatible act A B₀ ψ p g) :
    SourceWitness act A B₀ ψ p I ≃
      TargetWitness act A B₀ ψ p g I where
  toFun := fun x =>
    ⟨p x.1,
      p.map_source x.2.1,
      by
        change (p x.1).base ∈ g '' I.carrier
        refine ⟨x.1.base, x.2.2, ?_⟩
        exact hcompat.2 x.1 x.2.1⟩
  invFun := fun y => by
    let x : WitnessVertex act A B₀ ψ :=
      p.toPartialEquiv.symm y.1
    have hxSource : x ∈ p.source :=
      p.toPartialEquiv.symm.map_source y.2.1
    exact
      ⟨x, hxSource, by
        have hpx : p x = y.1 :=
          p.toPartialEquiv.right_inv y.2.1
        have hgbase :
            g x.base = y.1.base := by
          rw [hcompat.2 x hxSource]
          exact
            congrArg
              (fun w : WitnessVertex act A B₀ ψ => w.base) hpx
        rcases y.2.2 with ⟨b, hbI, hgb⟩
        have hxb : x.base = b := by
          have h :=
            congrArg
              (fun t => Structure.Automorphism.symm g t)
              (hgbase.trans hgb.symm)
          simpa using h
        exact hxb ▸ hbI⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact p.toPartialEquiv.left_inv x.2.1
  right_inv := by
    intro y
    apply Subtype.ext
    exact p.toPartialEquiv.right_inv y.2.1

/-- Used source labels. -/
def usedSourceLabels
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (I : BadIrreducible act A B₀ ψ) :
    Set (BadLabel act A B₀ ψ I) :=
  Set.range (sourceLabelMap act A B₀ ψ p I)

/-- Used target labels. -/
def usedTargetLabels
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ) :
    Set
      (BadLabel act A B₀ ψ
        (I.transport act A B₀ ψ g)) :=
  Set.range (targetLabelMap act A B₀ ψ p g I)

/-- Source witness fibres are equivalent to the used source labels. -/
noncomputable def sourceWitnessLabelEquiv
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (I : BadIrreducible act A B₀ ψ)
    (hgen : WitnessSetGeneric act A B₀ ψ p.source) :
    SourceWitness act A B₀ ψ p I ≃
      usedSourceLabels act A B₀ ψ p I :=
  Equiv.ofBijective
    (fun x =>
      ⟨sourceLabelMap act A B₀ ψ p I x,
        ⟨x, rfl⟩⟩)
    ⟨by
      intro x y h
      apply sourceLabelMap_injective act A B₀ ψ p I hgen
      exact congrArg Subtype.val h,
     by
      rintro ⟨l, x, rfl⟩
      exact ⟨x, rfl⟩⟩

/-- Target witness fibres are equivalent to the used target labels. -/
noncomputable def targetWitnessLabelEquiv
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hgen : WitnessSetGeneric act A B₀ ψ p.target) :
    TargetWitness act A B₀ ψ p g I ≃
      usedTargetLabels act A B₀ ψ p g I :=
  Equiv.ofBijective
    (fun x =>
      ⟨targetLabelMap act A B₀ ψ p g I x,
        ⟨x, rfl⟩⟩)
    ⟨by
      intro x y h
      apply targetLabelMap_injective
        act A B₀ ψ p g I hgen
      exact congrArg Subtype.val h,
     by
      rintro ⟨l, x, rfl⟩
      exact ⟨x, rfl⟩⟩

/-- The label bijection prescribed by the partial witness automorphism on the
labels which actually occur in its source. -/
noncomputable def usedLabelEquiv
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g) :
    usedSourceLabels act A B₀ ψ p I ≃
      usedTargetLabels act A B₀ ψ p g I :=
  (sourceWitnessLabelEquiv act A B₀ ψ p I hsource).symm.trans
    ((sourceTargetWitnessEquiv act A B₀ ψ p g I hcompat).trans
      (targetWitnessLabelEquiv act A B₀ ψ p g I htarget))

end Faithful
end AllThoseEPPA
