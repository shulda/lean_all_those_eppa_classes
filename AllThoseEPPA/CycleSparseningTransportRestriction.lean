import AllThoseEPPA.CycleSparseningStructureTransport

/-!
# Naturality of cycle-valuation transport with restriction

This follows the already checked faithful valuation-structure transport
argument, reusing its equivalences of one-point closures and the
commutation of closure transport with closure inclusions.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Transporting a cycle valuation structure then restricting it gives the
same structure as restricting first and transporting afterwards. -/
theorem ValuationStructure.transport_restrict
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    {x y : V}
    (W : ValuationStructure B₀ E x)
    (hy : y ∈ B₀.closureAtSet x) :
    ValuationStructure.transport act B₀ E g hfix
        (W.restrict B₀ E y hy) =
      (ValuationStructure.transport act B₀ E g hfix W).restrict
        B₀ E (g y)
        (Faithful.automorphism_maps_closureAtSet act B₀ g hy) := by
  apply Subtype.ext
  funext z
  let eY := Faithful.closureTransportEquiv act B₀ g y
  let z0 := eY.symm z
  have hz : eY z0 = z := eY.apply_symm_apply z
  rw [← hz]
  change
    valuationAssignmentEquiv act B₀ E g hfix y
        (W.restrict B₀ E y hy).1
        (eY z0) =
      valuationAssignmentEquiv act B₀ E g hfix x W.1
        (closureInclusion B₀
          (Faithful.automorphism_maps_closureAtSet act B₀ g hy)
          (eY z0))
  rw [valuationAssignmentEquiv_apply_transport
    act B₀ E g hfix y (W.restrict B₀ E y hy).1 z0]
  let T := valuationAssignmentEquiv act B₀ E g hfix x W.1
  let t₂ := Faithful.closureTransportEquiv act B₀ g x
      (closureInclusion B₀ hy z0)
  let t₁ := closureInclusion B₀
      (Faithful.automorphism_maps_closureAtSet act B₀ g hy)
      (eY z0)
  have ht : t₂ = t₁ := by
    exact Faithful.closureTransportEquiv_closureInclusion
      act B₀ g hy z0
  have hdep : HEq (T t₂) (T t₁) := by
    have hp :
        (⟨t₂, T t₂⟩ :
          Σ t : B₀.closureAtSet (g x),
            ValuationFunction B₀ E t.1) = ⟨t₁, T t₁⟩ :=
      congrArg
        (fun t =>
          (⟨t, T t⟩ :
            Σ s : B₀.closureAtSet (g x),
              ValuationFunction B₀ E s.1))
        ht
    exact (Sigma.mk.inj_iff.mp hp).2
  have hr :=
    valuationAssignmentEquiv_apply_transport
      act B₀ E g hfix x W.1
      (closureInclusion B₀ hy z0)
  have hleft :
      HEq
        (valuationFunctionTransportEquiv act B₀ E g hfix z0.1
          ((W.restrict B₀ E y hy).1 z0))
        (T t₂) := by
    exact heq_of_eq hr.symm
  exact eq_of_heq (hleft.trans hdep)

end Sparsening
end AllThoseEPPA
