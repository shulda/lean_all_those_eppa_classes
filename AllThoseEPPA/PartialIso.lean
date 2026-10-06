import Mathlib.Logic.Equiv.PartialEquiv
import AllThoseEPPA.Substructure

/-!
# Partial isomorphisms

A partial isomorphism is represented by a `PartialEquiv` on the vertex
carriers, together with a language permutation and the assertion that its
source and target are closed substructures and that it is an isomorphism
between them.

Using `PartialEquiv` avoids dependent-type transport problems when composing
isomorphisms between induced subtype structures.
-/

namespace AllThoseEPPA

universe u v w z

namespace Structure

variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable (act : L.Action Γ)
variable {V : Type w} {W : Type z}

/-- A partial isomorphism between Γ_L-structures. -/
structure PartialIsomorphism (A : Structure L V) (B : Structure L W) where
  lang : Γ
  toPartialEquiv : PartialEquiv V W
  source_closed : A.IsClosed toPartialEquiv.source
  target_closed : B.IsClosed toPartialEquiv.target
  map_rel_iff :
    ∀ {n : ℕ} (R : L.RelSymbol n) (x : Fin n → V),
      (∀ i, x i ∈ toPartialEquiv.source) →
      (B.rel (act.onRel lang R) (toPartialEquiv ∘ x) ↔ A.rel R x)
  map_func :
    ∀ {n : ℕ} (F : L.FuncSymbol n) (x : Fin n → V),
      (∀ i, x i ∈ toPartialEquiv.source) →
      imageSet toPartialEquiv (A.func F x) =
        B.func (act.onFunc lang F) (toPartialEquiv ∘ x)

instance {A : Structure L V} {B : Structure L W} :
    CoeFun (PartialIsomorphism act A B) (fun _ => V → W) :=
  ⟨fun f => f.toPartialEquiv⟩

namespace PartialIsomorphism

variable {act : L.Action Γ}
variable {A : Structure L V} {B : Structure L W}

/-- Domain of a partial isomorphism. -/
def source (f : PartialIsomorphism act A B) : Set V :=
  f.toPartialEquiv.source

/-- Range of a partial isomorphism. -/
def target (f : PartialIsomorphism act A B) : Set W :=
  f.toPartialEquiv.target

theorem map_source (f : PartialIsomorphism act A B) {x : V}
    (hx : x ∈ f.source) :
    f x ∈ f.target :=
  f.toPartialEquiv.map_source hx

theorem left_inv (f : PartialIsomorphism act A B) {x : V}
    (hx : x ∈ f.source) :
    f.toPartialEquiv.symm (f x) = x :=
  f.toPartialEquiv.left_inv hx

theorem right_inv (f : PartialIsomorphism act A B) {y : W}
    (hy : y ∈ f.target) :
    f (f.toPartialEquiv.symm y) = y :=
  f.toPartialEquiv.right_inv hy

end PartialIsomorphism
end Structure
end AllThoseEPPA
