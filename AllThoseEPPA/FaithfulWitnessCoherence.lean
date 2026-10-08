import AllThoseEPPA.FaithfulValuationCoherence
import AllThoseEPPA.FaithfulWitnessAutomorphism

/-!
# Coherence of faithful witness transport
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

/-- Transport of faithful witness vertices is coherent under composition of
compatible partial automorphisms and base automorphisms. -/
theorem WitnessVertex.transport_comp [Finite β]
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (gp gq : Structure.Automorphism act B₀)
    (ht : p.target = q.source)
    (hsp : WitnessSetGeneric act A B₀ ψ p.source)
    (htp : WitnessSetGeneric act A B₀ ψ p.target)
    (hsq : WitnessSetGeneric act A B₀ ψ q.source)
    (htq : WitnessSetGeneric act A B₀ ψ q.target)
    (hcp : BaseCompatible act A B₀ ψ p gp)
    (hcq : BaseCompatible act A B₀ ψ q gq)
    (hss :
      WitnessSetGeneric act A B₀ ψ (q.comp p ht).source)
    (hst :
      WitnessSetGeneric act A B₀ ψ (q.comp p ht).target)
    (hcs :
      BaseCompatible act A B₀ ψ
        (q.comp p ht) (gq.comp gp))
    (x : WitnessVertex act A B₀ ψ) :
    WitnessVertex.transport act A B₀ ψ
        q gq hsq htq hcq
        (WitnessVertex.transport act A B₀ ψ
          p gp hsp htp hcp x) =
      WitnessVertex.transport act A B₀ ψ
        (q.comp p ht) (gq.comp gp)
        hss hst hcs x := by
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  exact heq_of_eq
    (ValuationStructure.transport_comp
      act A B₀ ψ p q gp gq ht
      hsp htp hsq htq hcp hcq
      hss hst hcs x.valuation)

/-- The lifted faithful witness automorphisms compose exactly. -/
theorem faithfulWitnessAutomorphism_comp [Finite β]
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (gp gq : Structure.Automorphism act B₀)
    (ht : p.target = q.source)
    (hsp : WitnessSetGeneric act A B₀ ψ p.source)
    (htp : WitnessSetGeneric act A B₀ ψ p.target)
    (hsq : WitnessSetGeneric act A B₀ ψ q.source)
    (htq : WitnessSetGeneric act A B₀ ψ q.target)
    (hcp : BaseCompatible act A B₀ ψ p gp)
    (hcq : BaseCompatible act A B₀ ψ q gq)
    (hss :
      WitnessSetGeneric act A B₀ ψ (q.comp p ht).source)
    (hst :
      WitnessSetGeneric act A B₀ ψ (q.comp p ht).target)
    (hcs :
      BaseCompatible act A B₀ ψ
        (q.comp p ht) (gq.comp gp)) :
    faithfulWitnessAutomorphism act A B₀ ψ
        (q.comp p ht) (gq.comp gp)
        hss hst hcs =
      (faithfulWitnessAutomorphism act A B₀ ψ
        q gq hsq htq hcq).comp
        (faithfulWitnessAutomorphism act A B₀ ψ
          p gp hsp htp hcp) := by
  apply Structure.Automorphism.ext_of_lang_apply
  · rfl
  · intro x
    change
      WitnessVertex.transport act A B₀ ψ
          (q.comp p ht) (gq.comp gp)
          hss hst hcs x =
        WitnessVertex.transport act A B₀ ψ
          q gq hsq htq hcq
          (WitnessVertex.transport act A B₀ ψ
            p gp hsp htp hcp x)
    exact
      (WitnessVertex.transport_comp
        act A B₀ ψ p q gp gq ht
        hsp htp hsq htq hcp hcq
        hss hst hcs x).symm

/-- Faithful witness transport depends only on the mathematical partial map
when the compatible base automorphism is fixed. -/
theorem WitnessVertex.transport_eq_of_equivalent [Finite β]
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsp : WitnessSetGeneric act A B₀ ψ p.source)
    (htp : WitnessSetGeneric act A B₀ ψ p.target)
    (hsq : WitnessSetGeneric act A B₀ ψ q.source)
    (htq : WitnessSetGeneric act A B₀ ψ q.target)
    (hcp : BaseCompatible act A B₀ ψ p g)
    (hcq : BaseCompatible act A B₀ ψ q g)
    (hpq : Structure.PartialIsomorphism.Equivalent p q)
    (x : WitnessVertex act A B₀ ψ) :
    WitnessVertex.transport act A B₀ ψ
        p g hsp htp hcp x =
      WitnessVertex.transport act A B₀ ψ
        q g hsq htq hcq x := by
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  exact heq_of_eq
    (ValuationStructure.transport_eq_of_equivalent
      act A B₀ ψ p q g
      hsp htp hsq htq hcp hcq hpq x.valuation)

/-- Consequently, the lifted faithful automorphism is invariant under
equivalent partial automorphisms for a fixed compatible base automorphism. -/
theorem faithfulWitnessAutomorphism_eq_of_equivalent [Finite β]
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsp : WitnessSetGeneric act A B₀ ψ p.source)
    (htp : WitnessSetGeneric act A B₀ ψ p.target)
    (hsq : WitnessSetGeneric act A B₀ ψ q.source)
    (htq : WitnessSetGeneric act A B₀ ψ q.target)
    (hcp : BaseCompatible act A B₀ ψ p g)
    (hcq : BaseCompatible act A B₀ ψ q g)
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    faithfulWitnessAutomorphism act A B₀ ψ
        p g hsp htp hcp =
      faithfulWitnessAutomorphism act A B₀ ψ
        q g hsq htq hcq := by
  apply Structure.Automorphism.ext_of_lang_apply
  · rfl
  · intro x
    change
      WitnessVertex.transport act A B₀ ψ
          p g hsp htp hcp x =
        WitnessVertex.transport act A B₀ ψ
          q g hsq htq hcq x
    exact
      WitnessVertex.transport_eq_of_equivalent
        act A B₀ ψ p q g
        hsp htp hsq htq hcp hcq hpq x


end Faithful
end AllThoseEPPA
