import AllThoseEPPA.FaithfulTransport
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sort

/-!
# Finite label types for the faithful construction
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

/-- An automorphism gives a bijection between the carriers of a bad
irreducible and its transported copy. -/
noncomputable def badCarrierEquiv
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ) :
    I.carrier ≃ (I.transport act A B₀ ψ g).carrier where
  toFun := fun x => ⟨g x.1, ⟨x.1, x.2, rfl⟩⟩
  invFun := fun y =>
    ⟨g.symm y.1, by
      rcases y.2 with ⟨x, hx, hxy⟩
      have h :
          g.symm y.1 = x := by
        rw [← hxy]
        simp
      simpa [h] using hx⟩
  left_inv := by
    intro x
    apply Subtype.ext
    simp
  right_inv := by
    intro y
    apply Subtype.ext
    simp

/-- A label is equivalently a carrier point different from the distinguished
hole. -/
def badLabelEquivCarrierNeHole
    (I : BadIrreducible act A B₀ ψ) :
    BadLabel act A B₀ ψ I ≃
      {x : I.carrier //
        x ≠
          (⟨I.hole act A B₀ ψ,
            I.hole_mem act A B₀ ψ⟩ : I.carrier)} where
  toFun := fun x =>
    ⟨⟨x.1, x.2.1⟩, by
      intro h
      apply x.2.2
      exact congrArg Subtype.val h⟩
  invFun := fun x =>
    ⟨x.1.1, x.1.2, by
      intro h
      apply x.2
      apply Subtype.ext
      exact h⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl

/-- The label type has one fewer element than the carrier of the bad
irreducible. -/
theorem badLabel_card [Finite β]
    (I : BadIrreducible act A B₀ ψ) :
    Fintype.card (BadLabel act A B₀ ψ I) =
      Fintype.card I.carrier - 1 := by
  classical
  letI : Fintype β := Fintype.ofFinite β
  letI : Fintype I.carrier := Fintype.ofFinite _
  letI : Fintype (BadLabel act A B₀ ψ I) := Fintype.ofFinite _
  let h :
      Fintype.card (BadLabel act A B₀ ψ I) =
        Fintype.card
          {x : I.carrier //
            x ≠
              (⟨I.hole act A B₀ ψ,
                I.hole_mem act A B₀ ψ⟩ : I.carrier)} :=
    Fintype.card_congr (badLabelEquivCarrierNeHole act A B₀ ψ I)
  rw [h]
  rw [Fintype.card_subtype_compl]
  rw [Fintype.card_subtype_eq]

/-- Transport preserves the cardinality of label types. -/
theorem badLabel_transport_card [Finite β]
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ) :
    Fintype.card (BadLabel act A B₀ ψ I) =
      Fintype.card
        (BadLabel act A B₀ ψ
          (I.transport act A B₀ ψ g)) := by
  classical
  letI : Fintype β := Fintype.ofFinite β
  letI : Fintype I.carrier := Fintype.ofFinite _
  letI :
      Fintype (I.transport act A B₀ ψ g).carrier :=
    Fintype.ofFinite _
  letI : Fintype (BadLabel act A B₀ ψ I) :=
    Fintype.ofFinite _
  letI :
      Fintype
        (BadLabel act A B₀ ψ
          (I.transport act A B₀ ψ g)) :=
    Fintype.ofFinite _
  rw [badLabel_card act A B₀ ψ I,
    badLabel_card act A B₀ ψ
      (I.transport act A B₀ ψ g)]
  exact congrArg (fun n => n - 1)
    (Fintype.card_congr (badCarrierEquiv act A B₀ ψ g I))

/-- A fixed Fintype structure for each bad-label type. -/
noncomputable def badLabelFintype [Finite β]
    (I : BadIrreducible act A B₀ ψ) :
    Fintype (BadLabel act A B₀ ψ I) :=
  Fintype.ofFinite _

/-- A fixed linear order on each bad-label type.  The mathematical
construction is independent of this auxiliary choice; it is used only to
complete partial bijections canonically. -/
noncomputable def badLabelLinearOrder [Finite β]
    (I : BadIrreducible act A B₀ ψ) :
    LinearOrder (BadLabel act A B₀ ψ I) := by
  letI : Fintype (BadLabel act A B₀ ψ I) :=
    badLabelFintype act A B₀ ψ I
  exact
    LinearOrder.lift'
      (Fintype.equivFin (BadLabel act A B₀ ψ I))
      (Fintype.equivFin (BadLabel act A B₀ ψ I)).injective

end Faithful
end AllThoseEPPA
