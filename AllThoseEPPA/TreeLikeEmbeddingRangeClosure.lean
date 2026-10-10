import AllThoseEPPA.Substructure

/-!
# Images of exact Γ-structure embeddings are closed substructures

Every exact Γ-structure embedding preserves all set-valued function
fibres by equality rather than just inclusion. Consequently its
image is automatically closed under all function values, even for
non-unary function symbols.

The concrete free amalgam built in the `TreeLikeAmalgam*`
modules will use this twice: both canonical embedded source
carriers are closed, and so is their common intersection. The
statement is useful independently of the chordal graph setting.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- The range of a **structure embedding**, unlike that of an
arbitrary homomorphism, is closed under every set-valued
function. There is no restriction on function arities. -/
theorem Embedding.range_isClosed
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Embedding act A B) :
    B.IsClosed (Set.range f.toFun) := by
  classical
  intro n F xs hxs y hy
  choose as has using hxs
  have hTuple : f.toFun ∘ as = xs := by
    funext i
    exact has i
  let F₀ : L.FuncSymbol n := act.onFunc f.lang⁻¹ F
  have hF : act.onFunc f.lang F₀ = F := by
    change act.onFunc f.lang (act.onFunc f.lang⁻¹ F) = F
    rw [← act.onFunc_mul]
    simp
  have hmap := f.map_func F₀ as
  rw [hF, hTuple] at hmap
  rw [← hmap] at hy
  obtain ⟨a, ha, hfa⟩ := hy
  exact ⟨a, hfa⟩

/-- Intersections of closed vertex sets are closed; this will
supply the intersection-closure field of a free decomposition
after the canonical side embeddings have been built. -/
theorem IsClosed.inter
    (B : Structure L W) (X Y : Set W)
    (hX : B.IsClosed X) (hY : B.IsClosed Y) :
    B.IsClosed (X ∩ Y) := by
  intro n F xs hxs z hz
  exact ⟨hX F xs (fun i => (hxs i).1) hz,
    hY F xs (fun i => (hxs i).2) hz⟩

end Structure
end AllThoseEPPA
