import AllThoseEPPA.TreeLikeAmalgamCarrier

/-!
# The universal map from an explicitly glued carrier

Two vertex maps h₁ : X → M and h₂ : Y → M agreeing on the
specified interface I induce a map from the actual
`AmalgamCarrier f g` to M. This is a pointwise pushout
universal property; the later structure-level glue lemma
must separately check Γ-language elements, relation preservation,
and set-valued function fibres.

Neither h₁ nor h₂ needs to be injective. The interface embeddings
f and g are injective in the tree-amalgamation applications.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x
variable {I : Type u} {X : Type v} {Y : Type w} {M : Type x}

/-- The map glued from compatible vertex maps on both sides. -/
def gluedCarrierMap
    (f : I → X) (g : I → Y)
    (h₁ : X → M) (h₂ : Y → M) :
    AmalgamCarrier f g → M
  | .inl x => h₁ x
  | .inr y => h₂ y.1

@[simp] theorem gluedCarrierMap_left
    (f : I → X) (g : I → Y)
    (h₁ : X → M) (h₂ : Y → M) (x : X) :
    gluedCarrierMap f g h₁ h₂ (amalgamLeft f g x) = h₁ x :=
  rfl

/-- On a right-hand vertex, the glued map agrees with h₂ as
soon as h₁ and h₂ coincide on the designated interface. -/
theorem gluedCarrierMap_right
    (f : I → X) (g : I → Y)
    (hg : Function.Injective g)
    (h₁ : X → M) (h₂ : Y → M)
    (hagree : ∀ c : I, h₁ (f c) = h₂ (g c))
    (y : Y) :
    gluedCarrierMap f g h₁ h₂ (amalgamRight f g y) = h₂ y := by
  classical
  by_cases hy : y ∈ Set.range g
  · obtain ⟨i, rfl⟩ := hy
    rw [amalgamRight_glued f g hg i]
    exact hagree i
  · rw [amalgamRight_outside f g y hy]
    rfl

/-- Uniqueness of maps from the glued carrier, for arbitrary
interfaces and possibly degenerate gluing. -/
theorem gluedCarrierMap_unique
    (f : I → X) (g : I → Y)
    (h₁ : X → M) (h₂ : Y → M)
    (t : AmalgamCarrier f g → M)
    (hleft : ∀ x : X, t (amalgamLeft f g x) = h₁ x)
    (hright : ∀ y : Y, t (amalgamRight f g y) = h₂ y) :
    t = gluedCarrierMap f g h₁ h₂ := by
  funext z
  cases z with
  | inl x =>
      exact hleft x
  | inr y =>
      have hr := hright y.1
      rw [amalgamRight_outside f g y.1 y.2] at hr
      simpa only [gluedCarrierMap] using hr

end TreeLike
end AllThoseEPPA
