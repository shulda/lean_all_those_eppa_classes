import AllThoseEPPA.CycleSparseningProjection
import AllThoseEPPA.UnaryFunctions

/-!
# Closed images under the cycle-sparsening projections

An arbitrary homomorphism need not carry a closed set to a closed
set: its function-value inclusions can be strict.  Each sparsening
projection is stronger, because it maps *every unary function fibre
onto the entire base fibre*.  This module exploits precisely that
property to allow successive projections of the chosen small
substructure in the proof of the restricted EPPA theorem.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {V : Type v} {W : Type w}

/-- If a map exactly preserves every unary function fibre, the image
of every closed set is closed, even if the map is not injective.
This is the key closure property not enjoyed by general
homomorphisms of structures with set-valued functions. -/
theorem imageSet_isClosed_of_exact_func
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hfun : ∀ {n : ℕ} (F : L.FuncSymbol n) (xs : Fin n → V),
      imageSet f (A.func F xs) = B.func F (f ∘ xs))
    (S : Set V)
    (hS : A.IsClosed S) :
    B.IsClosed (imageSet f S) := by
  intro n F ys hys z hz
  let i := UnaryFunctions.unaryIndex F
  obtain ⟨x, hx, hxy⟩ := hys i
  have hyconst : ys = fun _ => ys i :=
    UnaryFunctions.unaryTuple_eq_constant F ys
  have hysEq : ys = f ∘ (fun _ : Fin n => x) := by
    calc
      ys = fun _ => ys i := hyconst
      _ = fun _ => f x := by rw [← hxy]
      _ = f ∘ (fun _ : Fin n => x) := rfl
  have hzeq : z ∈ imageSet f (A.func F (fun _ : Fin n => x)) := by
    rw [hfun F (fun _ : Fin n => x)]
    exact hysEq ▸ hz
  obtain ⟨a, ha, rfl⟩ := hzeq
  exact ⟨a, hS F (fun _ : Fin n => x) (fun _ => hx) ha, rfl⟩

end Structure

namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w}

/-- The image of a closed subset of the cycle-sparsening witness
under its canonical projection is a closed subset of the base
structure. This enables iteration of the sparsening trichotomy
on the successive images of small closed substructures. -/
theorem sparsening_projection_image_isClosed
    (act : L.Action Γ) (B₀ : Structure L V)
    (E : L.RelSymbol 2)
    (S : Set (Sparsening.WitnessVertex B₀ E))
    (hS : (Sparsening.witnessStructure B₀ E).IsClosed S) :
    B₀.IsClosed (Set.image (fun w => w.base B₀ E) S) := by
  let f : Sparsening.WitnessVertex B₀ E → V :=
    fun w => w.base B₀ E
  have hf : ∀ {n : ℕ} (F : L.FuncSymbol n)
      (xs : Fin n → Sparsening.WitnessVertex B₀ E),
      Structure.imageSet f
        ((Sparsening.witnessStructure B₀ E).func F xs) =
        B₀.func F (f ∘ xs) := by
    intro n F xs
    simpa [f, Sparsening.projection] using
      (Sparsening.projection_map_func_eq act B₀ E F xs)
  intro n F xs hxs
  exact (Structure.imageSet_isClosed_of_exact_func
    (Sparsening.witnessStructure B₀ E) B₀ f hf S hS) F xs hxs

end TreeLike
end AllThoseEPPA
