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


variable {X : Type*} {C : Structure L X}

/-- Composition of partial isomorphisms when the range of the first is exactly
the domain of the second.  This is the composition used in coherent triples in
the paper. -/
def comp (g : PartialIsomorphism act B C)
    (f : PartialIsomorphism act A B)
    (h : f.target = g.source) :
    PartialIsomorphism act A C where
  lang := g.lang * f.lang
  toPartialEquiv := f.toPartialEquiv.trans' g.toPartialEquiv h
  source_closed := f.source_closed
  target_closed := g.target_closed
  map_rel_iff := by
    intro n R x hx
    have hxf : ∀ i, x i ∈ f.toPartialEquiv.source := by
      intro i
      simpa [PartialEquiv.trans'] using hx i
    have h' : f.toPartialEquiv.target = g.toPartialEquiv.source := h
    have hxg : ∀ i, f.toPartialEquiv (x i) ∈ g.toPartialEquiv.source := by
      intro i
      rw [← h']
      exact f.toPartialEquiv.map_source (hxf i)
    have hg :=
      g.map_rel_iff (act.onRel f.lang R) (f.toPartialEquiv ∘ x) hxg
    have hf := f.map_rel_iff R x hxf
    simpa [PartialEquiv.trans', Language.Action.onRel_mul,
      Function.comp_assoc] using hg.trans hf
  map_func := by
    intro n F x hx
    have hxf : ∀ i, x i ∈ f.toPartialEquiv.source := by
      intro i
      simpa [PartialEquiv.trans'] using hx i
    have h' : f.toPartialEquiv.target = g.toPartialEquiv.source := h
    have hxg : ∀ i, f.toPartialEquiv (x i) ∈ g.toPartialEquiv.source := by
      intro i
      rw [← h']
      exact f.toPartialEquiv.map_source (hxf i)
    change
      imageSet (g.toPartialEquiv ∘ f.toPartialEquiv) (A.func F x) =
        C.func (act.onFunc (g.lang * f.lang) F)
          ((g.toPartialEquiv ∘ f.toPartialEquiv) ∘ x)
    rw [imageSet_comp]
    rw [f.map_func F x hxf]
    rw [g.map_func (act.onFunc f.lang F) (f.toPartialEquiv ∘ x) hxg]
    simp [Language.Action.onFunc_mul, Function.comp_assoc]

/-- A coherent triple of partial automorphisms, as in the paper. -/
def CoherentTriple {A : Structure L V}
    (f g h : PartialIsomorphism act A A) : Prop :=
  ∃ htg : f.target = g.source, h = g.comp f htg

/-- Two partial automorphisms form a coherent pair if they occur as the first
two members of a coherent triple. -/
def CoherentPair {A : Structure L V}
    (f g : PartialIsomorphism act A A) : Prop :=
  ∃ h, CoherentTriple f g h

end PartialIsomorphism
end Structure
end AllThoseEPPA
