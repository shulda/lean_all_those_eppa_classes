import AllThoseEPPA.TreeLikeFreshBinaryLanguage
import AllThoseEPPA.Map

/-!
# Complete fresh-binary expansions and their old-language reduct

The fresh fixed binary relation records inequality of the two coordinates.
At arity two this is precisely the complete loopless graph. Old relations
and all set-valued functions are unchanged.

Exact Γ-embeddings lift to expansions since injective vertex maps preserve
and reflect the new inequality relation. Homomorphisms and embeddings of
expanded structures descend to the old-language reduct. These are the
first genuine structure-level bridges required to remove the auxiliary E
from the fixed-E restricted EPPA construction.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x
variable {L : Language.{u}} {V : Type v} {W : Type w}
variable {Γ : Type x} [Group Γ]

/-- Add the genuinely fresh Γ-fixed binary E, interpreted as the complete
loopless graph on the carrier. All original symbols keep their meanings. -/
def withCompleteFixedBinary (A : Structure L V) :
    Structure L.withFixedBinaryRel V where
  rel := fun {_n} R xs =>
    match R with
    | .inl r => A.rel r xs
    | .inr _ => Function.Injective xs
  func := fun {_n} F xs => A.func F xs

/-- Forget precisely the newly adjoined E-symbol. -/
def forgetFixedBinary (B : Structure L.withFixedBinaryRel V) :
    Structure L V where
  rel := fun {_n} R xs => B.rel (.inl R) xs
  func := fun {_n} F xs => B.func F xs

@[simp] theorem forget_withCompleteFixedBinary (A : Structure L V) :
    (A.withCompleteFixedBinary).forgetFixedBinary = A := rfl

@[simp] theorem withCompleteFixedBinary_oldRel
    (A : Structure L V) {n : ℕ}
    (R : L.RelSymbol n) (xs : Fin n → V) :
    A.withCompleteFixedBinary.rel (.inl R) xs = A.rel R xs := rfl

@[simp] theorem withCompleteFixedBinary_freshRel
    (A : Structure L V) (xs : Fin 2 → V) :
    A.withCompleteFixedBinary.rel
      (L.withFixedBinaryRel.freshE) xs ↔ Function.Injective xs :=
  Iff.rfl

namespace Embedding

/-- Exact Γ-embeddings preserve and reflect the newly added complete E. -/
def withCompleteFixedBinary
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (e : Embedding act A B) :
    Embedding act.withFixedBinaryRel
      A.withCompleteFixedBinary B.withCompleteFixedBinary where
  lang := e.lang
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := by
    intro n R xs
    cases R with
    | inl r =>
        exact e.map_rel_iff r xs
    | inr _ =>
        change Function.Injective (e.toFun ∘ xs) ↔ Function.Injective xs
        constructor
        · intro h i j hij
          exact h (congrArg e.toFun hij)
        · intro h i j hij
          exact h (e.injective hij)
  map_func := by
    intro n F xs
    exact e.map_func F xs

/-- Every embedding in the expanded language restricts to an embedding
of the old-language reducts, with the same vertex and language components. -/
def forgetFixedBinary
    (act : L.Action Γ)
    {B : Structure L.withFixedBinaryRel V}
    {C : Structure L.withFixedBinaryRel W}
    (e : Embedding act.withFixedBinaryRel B C) :
    Embedding act B.forgetFixedBinary C.forgetFixedBinary where
  lang := e.lang
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := by
    intro n R xs
    exact e.map_rel_iff (.inl R) xs
  map_func := by
    intro n F xs
    exact e.map_func F xs

end Embedding

namespace Homomorphism

/-- Forgetting the fresh E preserves arbitrary Γ-homomorphisms, even when
their underlying vertex map is noninjective. -/
def forgetFixedBinary
    (act : L.Action Γ)
    {B : Structure L.withFixedBinaryRel V}
    {C : Structure L.withFixedBinaryRel W}
    (f : Homomorphism act.withFixedBinaryRel B C) :
    Homomorphism act B.forgetFixedBinary C.forgetFixedBinary where
  lang := f.lang
  toFun := f.toFun
  map_rel := by
    intro n R xs hx
    exact f.map_rel (.inl R) xs hx
  map_func := by
    intro n F xs
    exact f.map_func F xs

end Homomorphism
end Structure
end AllThoseEPPA
