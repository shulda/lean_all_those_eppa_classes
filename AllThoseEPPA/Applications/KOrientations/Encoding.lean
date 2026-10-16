import AllThoseEPPA.Applications.KOrientations.ClosureMinimal
import AllThoseEPPA.Relabelling
import Mathlib.Algebra.Group.PUnit

/-!
# Exact language/structure encoding of \(s\)- and \(d\)-closures

The \(s\)-language has one binary directed-edge symbol and one unary
set-valued successor function. Its unary-function scope is exactly
the scope of the already verified unrestricted EPPA theorem.

The \(d\)-language has the same directed edges and successor function,
together with a distinct \(n\)-ary root-fibre function for every
positive natural \(n\). The \(d\)-language is **not** a unary-function
language and is *never* passed directly to the main EPPA theorem.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- Both languages share the same binary directed-edge symbol. -/
inductive EdgeSymbol : ℕ → Type
  | edge : EdgeSymbol 2

/-- The successor-closure unary function. -/
inductive SuccessorSymbol : ℕ → Type
  | successor : SuccessorSymbol 1

/-- Successor function plus all nonzero-arity root-fibre functions. -/
inductive DFunctionSymbol : ℕ → Type
  | successor : DFunctionSymbol 1
  | fiber (n : ℕ) (hpos : 0 < n) : DFunctionSymbol n

/-- The unary-function language of the first-stage EPPA construction. -/
def successorLanguage : Language where
  RelSymbol := EdgeSymbol
  FuncSymbol := SuccessorSymbol
  relArity_pos := by
    intro n R
    cases R
    decide

instance : successorLanguage.HasUnaryFunctions where
  arity_eq_one := by
    intro n F
    cases F
    rfl

/-- The full, generally non-unary \(d\)-closure language. -/
def dLanguage : Language where
  RelSymbol := EdgeSymbol
  FuncSymbol := DFunctionSymbol
  relArity_pos := by
    intro n R
    cases R
    decide

/-- Relabelling for the first, unary-function stage is trivial. -/
def successorAction : successorLanguage.Action PUnit.{1} :=
  Language.Action.trivial successorLanguage PUnit.{1}

/-- Interpret the binary edge and unary successor function exactly. -/
def successorStructure {V : Type u} (G : Digraph V) :
    Structure successorLanguage V where
  rel := by
    intro n R xs
    cases R with
    | edge =>
        exact G.edge (xs 0) (xs 1)
  func := by
    intro n F xs
    cases F with
    | successor =>
        exact G.successors (xs 0)

/-- Interpret every \(d\)-closure function by its full root fibre. -/
noncomputable def dStructure {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) : Structure dLanguage V where
  rel := by
    intro n R xs
    cases R with
    | edge =>
        exact G.edge (xs 0) (xs 1)
  func := by
    intro n F xs
    cases F with
    | successor =>
        exact G.successors (xs 0)
    | fiber n hpos =>
        exact G.dFiber k xs

@[simp] theorem successorStructure_edge {V : Type u}
    (G : Digraph V) (xs : Fin 2 → V) :
    (successorStructure G).rel EdgeSymbol.edge xs ↔
      G.edge (xs 0) (xs 1) :=
  Iff.rfl

@[simp] theorem successorStructure_successors {V : Type u}
    (G : Digraph V) (xs : Fin 1 → V) :
    (successorStructure G).func SuccessorSymbol.successor xs =
      G.successors (xs 0) :=
  rfl

@[simp] theorem dStructure_edge {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (xs : Fin 2 → V) :
    (dStructure G k).rel EdgeSymbol.edge xs ↔
      G.edge (xs 0) (xs 1) :=
  Iff.rfl

@[simp] theorem dStructure_successors {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (xs : Fin 1 → V) :
    (dStructure G k).func DFunctionSymbol.successor xs =
      G.successors (xs 0) :=
  rfl

@[simp] theorem dStructure_fiber {V : Type u} [Fintype V]
    (G : Digraph V) (k n : ℕ) (hpos : 0 < n)
    (xs : Fin n → V) :
    (dStructure G k).func (DFunctionSymbol.fiber n hpos) xs =
      G.dFiber k xs :=
  rfl

end AllThoseEPPA.Applications.KOrientations
