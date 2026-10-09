import AllThoseEPPA.CycleSparseningTrichotomy

/-!
# Canonical total lift of a generic partial automorphism

For coherence we package the unique source-supported global Boolean correction
as an actual total automorphism of the witness. Its definition only needs a
compatible base map; genericity is needed to prove the extension property.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- The canonical corrected lift of a compatible base automorphism,
using the unique cycle-wise flip prescribed on the source, and zero off it. -/
noncomputable def sparseningLiftAutomorphism [Finite V]
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g) :
    Structure.Automorphism act (witnessStructure B₀ E) :=
  (witnessFlipAutomorphism B₀ E
      (transportedSwitch act B₀ E g hfix
        (requiredSwitch act B₀ E p g hfix hcompat)) act).comp
    (baseAutomorphismLift act B₀ E g hfix)

/-- Its language component is precisely the base language permutation. -/
@[simp] theorem sparseningLiftAutomorphism_lang [Finite V]
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g) :
    (sparseningLiftAutomorphism act B₀ E p g hfix hcompat).lang =
      g.lang := by
  simp [sparseningLiftAutomorphism]

/-- The canonical lift is exactly the composition of base transport followed
by the prescribed flip on all witness vertices. -/
@[simp] theorem sparseningLiftAutomorphism_apply [Finite V]
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g)
    (w : WitnessVertex B₀ E) :
    sparseningLiftAutomorphism act B₀ E p g hfix hcompat w =
      (w.transport act B₀ E g hfix).flip B₀ E
        (transportedSwitch act B₀ E g hfix
          (requiredSwitch act B₀ E p g hfix hcompat)) :=
  rfl

/-- The source-supported canonical lift extends every generic partial
automorphism compatible with the chosen base automorphism. -/
theorem sparseningLiftAutomorphism_extends [Finite V]
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g)
    (hsource : WitnessSetGeneric B₀ E p.source)
    (htarget : WitnessSetGeneric B₀ E p.target) :
    Structure.ExtendsAlong act
      (Structure.Embedding.id (witnessStructure B₀ E))
      p (sparseningLiftAutomorphism act B₀ E p g hfix hcompat) :=
  correctedLift_extends act B₀ E p g hfix hcompat hsource htarget

end Sparsening
end AllThoseEPPA
