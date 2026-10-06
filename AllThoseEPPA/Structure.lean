import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic
import AllThoseEPPA.Language

/-!
# Γ_L-structures

A function symbol of arity n is interpreted, exactly as in the paper, as a
map from n-tuples of vertices to a set of vertices.
-/

namespace AllThoseEPPA

universe u v w

/-- An L-structure with relations and genuinely set-valued functions. -/
structure Structure (L : Language.{u}) (V : Type v) where
  rel : {n : ℕ} → L.RelSymbol n → (Fin n → V) → Prop
  func : {n : ℕ} → L.FuncSymbol n → (Fin n → V) → Set V

namespace Structure

variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Pointwise image of a set, used in the preservation law for functions. -/
def imageSet (f : V → W) (S : Set V) : Set W :=
  f '' S

@[simp] theorem mem_imageSet {f : V → W} {S : Set V} {y : W} :
    y ∈ imageSet f S ↔ ∃ x ∈ S, f x = y :=
  Iff.rfl

/-- Images under a composite map can be taken in two stages. -/
theorem imageSet_comp {X : Type*} (g : W → X) (f : V → W) (S : Set V) :
    imageSet (g ∘ f) S = imageSet g (imageSet f S) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩

end Structure
end AllThoseEPPA
