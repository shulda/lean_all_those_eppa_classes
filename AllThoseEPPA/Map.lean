import Mathlib.Data.Set.Image
import AllThoseEPPA.Structure

/-!
# Maps between Γ_L-structures

This follows Section 2 of the paper literally: a map has a language component
in Γ and a vertex component.  Homomorphisms preserve relations and map
function-value sets into the corresponding relabelled function-value sets.
Embeddings are injective and use equivalence/equality instead.
-/

namespace AllThoseEPPA

universe u v w z

namespace Structure

variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable (act : L.Action Γ)
variable {V : Type w} {W : Type z}

/-- A homomorphism of Γ_L-structures. -/
structure Homomorphism (A : Structure L V) (B : Structure L W) where
  lang : Γ
  toFun : V → W
  map_rel :
    ∀ {n : ℕ} (R : L.RelSymbol n) (x : Fin n → V),
      A.rel R x → B.rel (act.onRel lang R) (toFun ∘ x)
  map_func :
    ∀ {n : ℕ} (F : L.FuncSymbol n) (x : Fin n → V),
      imageSet toFun (A.func F x) ⊆
        B.func (act.onFunc lang F) (toFun ∘ x)

/-- An embedding of Γ_L-structures. -/
structure Embedding (A : Structure L V) (B : Structure L W) where
  lang : Γ
  toFun : V → W
  injective : Function.Injective toFun
  map_rel_iff :
    ∀ {n : ℕ} (R : L.RelSymbol n) (x : Fin n → V),
      B.rel (act.onRel lang R) (toFun ∘ x) ↔ A.rel R x
  map_func :
    ∀ {n : ℕ} (F : L.FuncSymbol n) (x : Fin n → V),
      imageSet toFun (A.func F x) =
        B.func (act.onFunc lang F) (toFun ∘ x)

instance {A : Structure L V} {B : Structure L W} :
    CoeFun (Homomorphism act A B) (fun _ => V → W) :=
  ⟨Homomorphism.toFun⟩

instance {A : Structure L V} {B : Structure L W} :
    CoeFun (Embedding act A B) (fun _ => V → W) :=
  ⟨Embedding.toFun⟩

namespace Homomorphism

variable {act : L.Action Γ}
variable {X : Type*}
variable {A : Structure L V} {B : Structure L W} {C : Structure L X}

/-- Identity homomorphism. -/
def id (A : Structure L V) : Homomorphism act A A where
  lang := 1
  toFun := _root_.id
  map_rel := by
    intro n R x hx
    simpa using hx
  map_func := by
    intro n F x
    intro y hy
    exact ⟨y, hy, rfl⟩

/-- Composition of homomorphisms.  The language component is composed in the
same order as in the paper: the language part of g ∘ f is g_L f_L. -/
def comp (g : Homomorphism act B C) (f : Homomorphism act A B) :
    Homomorphism act A C where
  lang := g.lang * f.lang
  toFun := g.toFun ∘ f.toFun
  map_rel := by
    intro n R x hx
    have h₁ := f.map_rel R x hx
    have h₂ := g.map_rel (act.onRel f.lang R) (f.toFun ∘ x) h₁
    simpa [Language.Action.onRel_mul, Function.comp_assoc] using h₂
  map_func := by
    intro n F x y hy
    rcases hy with ⟨a, ha, rfl⟩
    have hf :
        f a ∈ B.func (act.onFunc f.lang F) (f.toFun ∘ x) :=
      f.map_func F x ⟨a, ha, rfl⟩
    have hg :
        g (f a) ∈
          C.func (act.onFunc g.lang (act.onFunc f.lang F))
            (g.toFun ∘ (f.toFun ∘ x)) :=
      g.map_func (act.onFunc f.lang F) (f.toFun ∘ x) ⟨f a, hf, rfl⟩
    simpa [Language.Action.onFunc_mul, Function.comp_assoc] using hg

@[simp] theorem comp_apply (g : Homomorphism act B C)
    (f : Homomorphism act A B) (x : V) :
    g.comp f x = g (f x) :=
  rfl

end Homomorphism

namespace Embedding

variable {act : L.Action Γ}
variable {A : Structure L V} {B : Structure L W}

/-- Every embedding is in particular a homomorphism. -/
def toHomomorphism (f : Embedding act A B) : Homomorphism act A B where
  lang := f.lang
  toFun := f.toFun
  map_rel := by
    intro n R x hx
    exact (f.map_rel_iff R x).2 hx
  map_func := by
    intro n F x
    rw [f.map_func F x]

/-- Identity embedding. -/
def id (A : Structure L V) : Embedding act A A where
  lang := 1
  toFun := _root_.id
  injective := Function.injective_id
  map_rel_iff := by
    intro n R x
    simp
  map_func := by
    intro n F x
    ext y
    simp [imageSet]

end Embedding

end Structure
end AllThoseEPPA
