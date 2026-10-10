import Mathlib.Logic.Equiv.Sum
import AllThoseEPPA.Language

/-!
# Extend a Γ-language by a fresh globally fixed binary relation

The proof of the unrestricted version of Theorem thm:maintree
starts with a language L having arbitrary relations and
unary set-valued functions. It must add a NEW binary
relation E, fixed under all language permutations, before
applying the cycle-sparsening construction.

This module makes that language extension explicit:
the old relation symbols are kept as the left summand,
and one new binary symbol is represented by the
right summand (available only at arity two).
Function symbols are literally unchanged.

The original Γ-action is extended componentwise on
the old symbols and trivially on the new E symbol;
we verify that this is a genuine group action.
The unary-function-language assumption is preserved.

This is language infrastructure only: expansion and
reduct of Γ-structures, EPPA witnesses and tree
amalgamations are separate proof obligations.
-/

namespace AllThoseEPPA
namespace Language

universe u v
variable {L : Language.{u}} {Γ : Type v} [Group Γ]

/-- Extend a language by precisely one new binary
relation symbol, preserving every old relation/function
symbol and its arity. -/
def withFixedBinaryRel (L : Language.{u}) : Language.{u} where
  RelSymbol := fun n => Sum (L.RelSymbol n)
    (Subtype (fun (_ : PUnit.{u+1}) => n = 2))
  FuncSymbol := L.FuncSymbol
  relArity_pos := by
    intro n R
    cases R with
    | inl r =>
        exact L.relArity_pos r
    | inr e =>
        have hn : n = 2 := e.2
        subst n
        decide

/-- The distinguished fresh relation E has arity two. -/
def withFixedBinaryRel.freshE (L : Language.{u}) :
    L.withFixedBinaryRel.RelSymbol 2 :=
  Sum.inr ⟨PUnit.unit, rfl⟩

/-- Old relations embed canonically as the first summand. -/
def withFixedBinaryRel.oldRelation (L : Language.{u})
    {n : ℕ} (R : L.RelSymbol n) :
    L.withFixedBinaryRel.RelSymbol n :=
  Sum.inl R

/-- The old group action extended by *fixing the fresh
binary relation E pointwise*. This is an actual monoid
homomorphism into the permutation group at each arity. -/
def Action.withFixedBinaryRel
    (act : L.Action Γ) : L.withFixedBinaryRel.Action Γ where
  rel := fun n =>
    { toFun := fun g =>
        Equiv.sumCongr (act.rel n g) (Equiv.refl _)
      map_one' := by
        apply Equiv.ext
        intro x
        cases x with
        | inl r =>
            simp
            rfl
        | inr e => rfl
      map_mul' := by
        intro g h
        apply Equiv.ext
        intro x
        cases x with
        | inl r =>
            simp
            rfl
        | inr e => rfl }
  func := act.func

/-- The extended action really restricts to the original
action on all old relation symbols. -/
@[simp] theorem Action.withFixedBinaryRel_onOld
    (act : L.Action Γ)
    (g : Γ) {n : ℕ} (R : L.RelSymbol n) :
    (act.withFixedBinaryRel).onRel g
      (withFixedBinaryRel.oldRelation L R) =
        withFixedBinaryRel.oldRelation L (act.onRel g R) :=
  rfl

/-- The new binary relation is fixed by EVERY element
of the Γ-language action, as required by lem:sparsen. -/
@[simp] theorem Action.withFixedBinaryRel_onFresh
    (act : L.Action Γ) (g : Γ) :
    (act.withFixedBinaryRel).onRel g
      (withFixedBinaryRel.freshE L) =
        withFixedBinaryRel.freshE L :=
  rfl

/-- The extended language has exactly the same function
symbol families as the original language. -/
@[simp] theorem Action.withFixedBinaryRel_onFunc
    (act : L.Action Γ) (g : Γ)
    {n : ℕ} (F : L.FuncSymbol n) :
    (act.withFixedBinaryRel).onFunc g F = act.onFunc g F :=
  rfl

/-- Adding the fresh fixed binary relation preserves the
unary-only restriction on function arities. -/
instance (L : Language.{u}) [L.HasUnaryFunctions] :
    L.withFixedBinaryRel.HasUnaryFunctions where
  arity_eq_one := by
    intro n F
    exact HasUnaryFunctions.arity_eq_one (L := L) F

end Language
end AllThoseEPPA
