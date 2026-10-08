import AllThoseEPPA.FaithfulValuationTransport

/-!
# Genericity under faithful valuation transport
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

/-- Transport a valuation point by transporting its base point and its whole
valuation function. -/
noncomputable def transportValuationPoint [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (q : ValuationPoint act A B₀ ψ) :
    ValuationPoint act A B₀ ψ :=
  ⟨g q.1,
    valuationFunctionEquiv act A B₀ ψ
      p g hsource htarget hcompat q.1 q.2⟩

@[simp] theorem transportValuationPoint_base [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (q : ValuationPoint act A B₀ ψ) :
    (transportValuationPoint act A B₀ ψ
      p g hsource htarget hcompat q).1 = g q.1 :=
  rfl

/-- Genericity of valuation points is preserved by the faithful label
transport. -/
theorem areGeneric_transport [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    {q r : ValuationPoint act A B₀ ψ}
    (hqr : AreGeneric act A B₀ ψ q r) :
    AreGeneric act A B₀ ψ
      (transportValuationPoint act A B₀ ψ
        p g hsource htarget hcompat q)
      (transportValuationPoint act A B₀ ψ
        p g hsource htarget hcompat r) := by
  classical
  rcases hqr with hEq | ⟨hbase, hlabels⟩
  · subst r
    exact Or.inl rfl
  · right
    refine ⟨?_, ?_⟩
    · intro hgr
      apply hbase
      have h :=
        congrArg
          (fun x => Structure.Automorphism.symm g x) hgr
      simpa using h
    · intro J hqJ hrJ
      let I : BadIrreducible act A B₀ ψ :=
        J.transport act A B₀ ψ g.symm
      have hqI : q.1 ∈ I.carrier := by
        change q.1 ∈ g.symm '' J.carrier
        refine ⟨g q.1, hqJ, ?_⟩
        simp
      have hrI : r.1 ∈ I.carrier := by
        change r.1 ∈ g.symm '' J.carrier
        refine ⟨g r.1, hrJ, ?_⟩
        simp
      let Iq : BadAt act A B₀ ψ q.1 :=
        ⟨I, hqI⟩
      let Ir : BadAt act A B₀ ψ r.1 :=
        ⟨I, hrI⟩
      have hJq :
          badAtEquiv act A B₀ ψ g q.1 Iq =
            (⟨J, hqJ⟩ :
              BadAt act A B₀ ψ (g q.1)) := by
        apply Subtype.ext
        exact
          BadIrreducible.transport_transport_symm
            act A B₀ ψ g J
      have hJr :
          badAtEquiv act A B₀ ψ g r.1 Ir =
            (⟨J, hrJ⟩ :
              BadAt act A B₀ ψ (g r.1)) := by
        apply Subtype.ext
        exact
          BadIrreducible.transport_transport_symm
            act A B₀ ψ g J
      intro htargetEq
      have htargetEq' :
          (valuationFunctionEquiv act A B₀ ψ
              p g hsource htarget hcompat q.1 q.2
              (badAtEquiv act A B₀ ψ g q.1 Iq)).1 =
            (valuationFunctionEquiv act A B₀ ψ
              p g hsource htarget hcompat r.1 r.2
              (badAtEquiv act A B₀ ψ g r.1 Ir)).1 := by
        rw [hJq, hJr]
        exact htargetEq
      rw [
        valuationFunctionEquiv_apply_transport
          act A B₀ ψ p g hsource htarget hcompat
          q.1 q.2 Iq,
        valuationFunctionEquiv_apply_transport
          act A B₀ ψ p g hsource htarget hcompat
          r.1 r.2 Ir] at htargetEq'
      have htargetLabelEq :
          labelExtension act A B₀ ψ p g I
              hsource htarget hcompat (q.2 Iq) =
            labelExtension act A B₀ ψ p g I
              hsource htarget hcompat (r.2 Ir) := by
        apply Subtype.ext
        exact htargetEq'
      have hsourceLabelEq :
          q.2 Iq = r.2 Ir :=
        (labelExtension act A B₀ ψ p g I
          hsource htarget hcompat).injective htargetLabelEq
      exact
        (hlabels I hqI hrI)
          (congrArg Subtype.val hsourceLabelEq)

end Faithful
end AllThoseEPPA
