import AllThoseEPPA.FaithfulWitnessFunctionTransport

/-!
# Lifted automorphisms of the faithful witness
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

/-- Lift a compatible base automorphism to a total automorphism of the
faithful witness. -/
noncomputable def faithfulWitnessAutomorphism [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g) :
    Structure.Automorphism act
      (witnessStructure act A B₀ ψ) where
  toPartialIsomorphism :=
    { lang := g.lang
      toPartialEquiv :=
        (witnessEquiv act A B₀ ψ
          p g hsource htarget hcompat).toPartialEquiv
      source_closed :=
        (witnessStructure act A B₀ ψ).isClosed_univ
      target_closed :=
        (witnessStructure act A B₀ ψ).isClosed_univ
      map_rel_iff := by
        intro n R ws hws
        exact
          witnessRelation_transport_iff
            act A B₀ ψ p g
            hsource htarget hcompat R ws
      map_func := by
        intro n F ws hws
        exact
          witnessFunction_transport
            act A B₀ ψ p g
            hsource htarget hcompat F ws }
  source_eq_univ := rfl
  target_eq_univ := rfl

@[simp] theorem faithfulWitnessAutomorphism_lang [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g) :
    (faithfulWitnessAutomorphism act A B₀ ψ
      p g hsource htarget hcompat).lang = g.lang :=
  rfl

@[simp] theorem faithfulWitnessAutomorphism_apply [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (w : WitnessVertex act A B₀ ψ) :
    faithfulWitnessAutomorphism act A B₀ ψ
        p g hsource htarget hcompat w =
      WitnessVertex.transport act A B₀ ψ
        p g hsource htarget hcompat w :=
  rfl

end Faithful
end AllThoseEPPA
