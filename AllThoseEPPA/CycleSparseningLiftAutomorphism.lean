import AllThoseEPPA.CycleSparseningWitnessFunctionTransport

/-!
# Lift of any base automorphism to the cycle-sparsening witness

No partial-automorphism constraints are imposed here: each base automorphism
acting on the distinguished relation E has a canonical (pure reindexing) lift.
The flip automorphisms can subsequently be composed with these lifts.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Any E-preserving base automorphism canonically acts on cycle valuations,
lifting to an automorphism of the full witness, including unary functions. -/
noncomputable def baseAutomorphismLift [Finite V]
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E) :
    Structure.Automorphism act (witnessStructure B₀ E) where
  toPartialIsomorphism :=
    { lang := g.lang
      toPartialEquiv := (witnessEquiv act B₀ E g hfix).toPartialEquiv
      source_closed := (witnessStructure B₀ E).isClosed_univ
      target_closed := (witnessStructure B₀ E).isClosed_univ
      map_rel_iff := by
        intro n R ws hws
        exact witnessRelation_transport_iff act B₀ E g hfix R ws
      map_func := by
        intro n F ws hws
        exact witnessFunction_transport act B₀ E g hfix F ws }
  source_eq_univ := rfl
  target_eq_univ := rfl

@[simp] theorem baseAutomorphismLift_lang [Finite V]
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E) :
    (baseAutomorphismLift act B₀ E g hfix).lang = g.lang :=
  rfl

@[simp] theorem baseAutomorphismLift_apply [Finite V]
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (w : WitnessVertex B₀ E) :
    baseAutomorphismLift act B₀ E g hfix w =
      w.transport act B₀ E g hfix :=
  rfl

end Sparsening
end AllThoseEPPA
