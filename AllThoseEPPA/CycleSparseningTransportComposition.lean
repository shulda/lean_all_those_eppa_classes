import AllThoseEPPA.CycleSparseningPartialExtension

/-!
# Functorial transport of indexed bad cycles and global switches

This algebraic lemma will be used in the coherent composition calculation.
-/

namespace AllThoseEPPA
namespace Structure
namespace BadCycleSequence

universe u v w
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {act : L.Action Γ}
variable {A : Structure L V} {E : L.RelSymbol 2}

/-- Consecutive transport of a displayed bad cycle equals transport along
the composite automorphism, with unchanged cycle-index order. -/
theorem transport_comp
    (c : BadCycleSequence A E)
    (h g : Automorphism act A)
    (hfix : act.FixesRel E) :
    (c.transport g hfix).transport h hfix =
      c.transport (h.comp g) hfix := by
  apply ext_vertex _ _ rfl
  apply heq_of_eq
  funext i
  rfl

end BadCycleSequence
end Structure

namespace Sparsening
universe u v w
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Transported Boolean switches form an action of the base automorphism
group, with composition in the order of the actual witness action. -/
theorem transportedSwitch_comp
    (h g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (s : Structure.BadCycleSequence B₀ E → Bool) :
    transportedSwitch act B₀ E (h.comp g) hfix s =
      transportedSwitch act B₀ E h hfix
        (transportedSwitch act B₀ E g hfix s) := by
  funext c
  rcases (Structure.BadCycleSequence.transportEquiv
      (h.comp g) hfix).surjective c with ⟨d, rfl⟩
  have ht :=
    Structure.BadCycleSequence.transport_comp d h g hfix
  calc
    transportedSwitch act B₀ E (h.comp g) hfix s
        (d.transport (h.comp g) hfix) = s d :=
      transportedSwitch_transport act B₀ E (h.comp g) hfix s d
    _ = transportedSwitch act B₀ E h hfix
          (transportedSwitch act B₀ E g hfix s)
          (d.transport (h.comp g) hfix) := by
      rw [← ht]
      rw [transportedSwitch_transport]
      rw [transportedSwitch_transport]

/-- Transport of a pointwise XOR switch equals XOR of its transports. -/
theorem transportedSwitch_sum
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (s t : Structure.BadCycleSequence B₀ E → Bool) :
    transportedSwitch act B₀ E g hfix (switchSum B₀ E s t) =
      switchSum B₀ E
        (transportedSwitch act B₀ E g hfix s)
        (transportedSwitch act B₀ E g hfix t) := by
  funext c
  rfl


end Sparsening
end AllThoseEPPA
