import AllThoseEPPA.FaithfulTransport

/-!
# Transport of one-point closures under base automorphisms
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

/-- A base automorphism maps a one-point closure into the closure of the
image point. -/
theorem automorphism_maps_closureAtSet
    (g : Structure.Automorphism act B₀)
    {x y : β} (hy : y ∈ B₀.closureAtSet x) :
    g y ∈ B₀.closureAtSet (g x) := by
  let T : Set β :=
    g.symm '' B₀.closureAtSet (g x)
  have hTclosed : B₀.IsClosed T :=
    automorphism_image_isClosed act B₀ g.symm
      (B₀.isClosed_closureSet {g x})
  have hxT : x ∈ T := by
    refine ⟨g x, B₀.mem_closureAtSet (g x), ?_⟩
    simp
  have hsub : B₀.closureAtSet x ⊆ T := by
    apply B₀.closureSet_minimal hTclosed
    intro z hz
    have hzx : z = x := by simpa using hz
    subst z
    exact hxT
  rcases hsub hy with ⟨z, hz, hzy⟩
  have hgz : g (g.symm z) = z := by simp
  have : g y = z := by
    rw [← hzy]
    simp
  simpa [this] using hz

/-- A base automorphism maps a one-point closure exactly onto the one-point
closure of the image point. -/
theorem automorphism_image_closureAtSet
    (g : Structure.Automorphism act B₀)
    (x : β) :
    g '' B₀.closureAtSet x =
      B₀.closureAtSet (g x) := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact automorphism_maps_closureAtSet act B₀ g hz
  · intro y hy
    have hpre :
        g.symm y ∈ B₀.closureAtSet x := by
      have h :=
        automorphism_maps_closureAtSet
          act B₀ g.symm hy
      simpa using h
    exact ⟨g.symm y, hpre, by simp⟩

/-- The induced bijection between one-point closure carriers. -/
noncomputable def closureTransportEquiv
    (g : Structure.Automorphism act B₀)
    (x : β) :
    B₀.closureAtSet x ≃
      B₀.closureAtSet (g x) where
  toFun := fun y =>
    ⟨g y.1,
      automorphism_maps_closureAtSet act B₀ g y.2⟩
  invFun := fun y =>
    ⟨g.symm y.1, by
      have h :=
        automorphism_maps_closureAtSet
          act B₀ g.symm y.2
      simpa using h⟩
  left_inv := by
    intro y
    apply Subtype.ext
    simp
  right_inv := by
    intro y
    apply Subtype.ext
    simp

@[simp] theorem closureTransportEquiv_apply_val
    (g : Structure.Automorphism act B₀)
    (x : β) (y : B₀.closureAtSet x) :
    (closureTransportEquiv act B₀ g x y).1 = g y.1 :=
  rfl

@[simp] theorem closureTransportEquiv_symm_apply_val
    (g : Structure.Automorphism act B₀)
    (x : β) (y : B₀.closureAtSet (g x)) :
    ((closureTransportEquiv act B₀ g x).symm y).1 =
      g.symm y.1 :=
  rfl

end Faithful
end AllThoseEPPA
