import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.GroupTheory.Perm.Basic

/-!
# Languages and language actions

The paper works with a language whose relation and function symbols have fixed
arities, together with a permutation group Γ_L preserving symbol type and
arity.

For Lean, symbols are indexed by arity.  Thus arity preservation by Γ_L is
encoded in the types rather than carried around as equality proofs.
-/

namespace AllThoseEPPA

universe u v

/-- A language of relation symbols and set-valued function symbols, indexed by
their arity.  This is equivalent to the paper's presentation by a set of
symbols equipped with an arity function. -/
structure Language where
  RelSymbol : ℕ → Type u
  FuncSymbol : ℕ → Type u
  /-- Relation symbols have positive arity, exactly as in the paper. -/
  relArity_pos : ∀ {n : ℕ}, RelSymbol n → 0 < n

namespace Language

/-- A language is relational when it has no function symbols. -/
class IsRelational (L : Language.{u}) : Prop where
  func_isEmpty : ∀ n : ℕ, IsEmpty (L.FuncSymbol n)

instance {L : Language.{u}} [L.IsRelational] {n : ℕ} :
    IsEmpty (L.FuncSymbol n) :=
  IsRelational.func_isEmpty n


/-- A language has unary functions if every function symbol has arity one.
This is the function-language scope used by the main constructions of the
paper. -/
class HasUnaryFunctions (L : Language.{u}) : Prop where
  arity_eq_one : ∀ {n : ℕ}, L.FuncSymbol n → n = 1

/-- The relational reduct of a language: keep all relation symbols and forget
all function symbols. -/
def relationalReduct (L : Language.{u}) : Language.{u} where
  RelSymbol := L.RelSymbol
  FuncSymbol := fun _ => PEmpty.{u + 1}
  relArity_pos := L.relArity_pos

instance (L : Language.{u}) : L.relationalReduct.IsRelational where
  func_isEmpty := fun _ => ⟨PEmpty.elim⟩

/-- A relation symbol bundled together with its arity. -/
abbrev AnyRelSymbol (L : Language.{u}) := Σ n, L.RelSymbol n

/-- The first coordinate of a relation tuple.  This is always defined because
relation symbols in the paper have positive arity. -/
def firstIndex {L : Language.{u}} {n : ℕ} (R : L.RelSymbol n) : Fin n :=
  ⟨0, L.relArity_pos R⟩

/-- An action of a group Γ on the symbols of a language, preserving symbol type
and arity.  Each arity is acted on separately, so arity preservation is
definitionally visible to Lean. -/
structure Action (L : Language.{u}) (Γ : Type v) [Group Γ] where
  rel : (n : ℕ) → Γ →* Equiv.Perm (L.RelSymbol n)
  func : (n : ℕ) → Γ →* Equiv.Perm (L.FuncSymbol n)


/-- The trivial action of any group on a language. -/
def Action.trivial (L : Language.{u}) (Γ : Type v) [Group Γ] :
    L.Action Γ where
  rel _ := 1
  func _ := 1

/-- Relabel a relation symbol by a group element. -/
def Action.onRel {L : Language.{u}} {Γ : Type v} [Group Γ]
    (A : L.Action Γ) {n : ℕ} (g : Γ) (R : L.RelSymbol n) :
    L.RelSymbol n :=
  A.rel n g R

/-- Relabel a function symbol by a group element. -/
def Action.onFunc {L : Language.{u}} {Γ : Type v} [Group Γ]
    (A : L.Action Γ) {n : ℕ} (g : Γ) (F : L.FuncSymbol n) :
    L.FuncSymbol n :=
  A.func n g F

@[simp] theorem Action.onRel_one {L : Language.{u}} {Γ : Type v} [Group Γ]
    (A : L.Action Γ) {n : ℕ} (R : L.RelSymbol n) :
    A.onRel (1 : Γ) R = R := by
  simp [Action.onRel]

@[simp] theorem Action.onFunc_one {L : Language.{u}} {Γ : Type v} [Group Γ]
    (A : L.Action Γ) {n : ℕ} (F : L.FuncSymbol n) :
    A.onFunc (1 : Γ) F = F := by
  simp [Action.onFunc]

@[simp] theorem Action.onRel_mul {L : Language.{u}} {Γ : Type v} [Group Γ]
    (A : L.Action Γ) {n : ℕ} (g h : Γ) (R : L.RelSymbol n) :
    A.onRel (g * h) R = A.onRel g (A.onRel h R) := by
  simp [Action.onRel]

/-- Relabelling a relation symbol does not change the distinguished first
coordinate of its tuple.  The two `Fin n` terms differ only in proof fields. -/
@[simp] theorem Action.firstIndex_onRel {L : Language.{u}} {Γ : Type v} [Group Γ]
    (A : L.Action Γ) {n : ℕ} (g : Γ) (R : L.RelSymbol n) :
    firstIndex (A.onRel g R) = firstIndex R := by
  apply Fin.ext
  rfl

@[simp] theorem Action.onFunc_mul {L : Language.{u}} {Γ : Type v} [Group Γ]
    (A : L.Action Γ) {n : ℕ} (g h : Γ) (F : L.FuncSymbol n) :
    A.onFunc (g * h) F = A.onFunc g (A.onFunc h F) := by
  simp [Action.onFunc]

end Language
end AllThoseEPPA
