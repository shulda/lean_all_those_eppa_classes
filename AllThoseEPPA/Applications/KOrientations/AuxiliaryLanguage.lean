import AllThoseEPPA.Applications.KOrientations.ClosedSubstructures

/-!
# Finite auxiliary language for the root sort

This is the second-stage language in the manuscript's two-level EPPA
construction. The non-root vertices of a finite template are encoded
as **relation labels** on tuples of roots, rather than as higher-arity
function values. Therefore the auxiliary language has only one unary
function symbol, as required by the public unrestricted EPPA theorem.

Each label P carries its complete, nonempty, ordered root set.
There are two relation symbols per label:

* R_P of arity |roots(P)|, which names the corresponding non-root;
* E_P of arity |roots(P)|+1, encoding an incoming edge from a root.

The permutation-group action and faithful coherent EPPA witness for
this language are introduced in subsequent modules.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- A non-root template vertex with a complete, nonempty enumeration
of its reachable roots. The predicate is **exactly** the condition
used in the manuscript's index set \(\mathfrak P\). -/
structure RootPattern {V : Type u} [Fintype V]
    (G : Digraph V) (k n : ℕ) where
  center : V
  nonroot : ¬ G.IsRoot k center
  positive : 0 < n
  tuple : Fin n → V
  injective : Function.Injective tuple
  roots_eq : G.roots k center = Set.range tuple

/-- The auxiliary relations have the arity prescribed by the label. -/
inductive AuxiliaryRel {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) : ℕ → Type u where
  | edge : AuxiliaryRel G k 2
  | root {n : ℕ} (P : RootPattern G k n) :
      AuxiliaryRel G k n
  | incoming {n : ℕ} (P : RootPattern G k n) :
      AuxiliaryRel G k (n + 1)

/-- The auxiliary root language keeps the unary successor function. -/
inductive AuxiliaryFunc (V : Type u) : ℕ → Type u where
  | successor : AuxiliaryFunc V 1

/-- An arity-indexed language with E, R_P, E_P and **unary** F. -/
def auxiliaryLanguage {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) : Language.{u} where
  RelSymbol := AuxiliaryRel G k
  FuncSymbol := AuxiliaryFunc V
  relArity_pos := by
    intro n R
    cases R with
    | edge =>
        decide
    | root P =>
        exact P.positive
    | incoming P =>
        exact Nat.succ_pos _

instance auxiliaryLanguage_hasUnaryFunctions {V : Type u}
    [Fintype V] (G : Digraph V) (k : ℕ) :
    (auxiliaryLanguage G k).HasUnaryFunctions where
  arity_eq_one := by
    intro n F
    cases F
    rfl

/-- Roots belonging to the distinguished template substructure. -/
abbrev RootsIn {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V) :=
  {r : V // r ∈ S ∧ G.IsRoot k r}

/-- The root-only auxiliary structure. A given R_P tuple is realized
exactly when P's centre belongs to S and the tuple enumerates P's
ordered roots. E_P additionally records the directed root-to-centre
edge. All function values stay in the root sort. -/
def auxiliaryRootStructure {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V) :
    Structure (auxiliaryLanguage G k) (RootsIn G k S) where
  rel := by
    intro n R xs
    cases R with
    | edge =>
        exact G.edge (xs 0).val (xs 1).val
    | root P =>
        exact P.center ∈ S ∧
          ∀ i, (xs i).val = P.tuple i
    | incoming P =>
        exact P.center ∈ S ∧
          G.edge (xs 0).val P.center ∧
          ∀ i, (xs (Fin.succ i)).val = P.tuple i
  func := by
    intro n F xs
    cases F with
    | successor =>
        exact {r | G.Reaches (xs 0).val r.val}

@[simp] theorem auxiliaryRootStructure_edge
    {V : Type u} [Fintype V] (G : Digraph V)
    (k : ℕ) (S : Set V) (xs : Fin 2 → RootsIn G k S) :
    (auxiliaryRootStructure G k S).rel AuxiliaryRel.edge xs ↔
      G.edge (xs 0).val (xs 1).val :=
  Iff.rfl

@[simp] theorem auxiliaryRootStructure_root
    {V : Type u} [Fintype V] (G : Digraph V)
    (k n : ℕ) (S : Set V) (P : RootPattern G k n)
    (xs : Fin n → RootsIn G k S) :
    (auxiliaryRootStructure G k S).rel (AuxiliaryRel.root P) xs ↔
      P.center ∈ S ∧ ∀ i, (xs i).val = P.tuple i :=
  Iff.rfl

@[simp] theorem auxiliaryRootStructure_incoming
    {V : Type u} [Fintype V] (G : Digraph V)
    (k n : ℕ) (S : Set V) (P : RootPattern G k n)
    (xs : Fin (n + 1) → RootsIn G k S) :
    (auxiliaryRootStructure G k S).rel (AuxiliaryRel.incoming P) xs ↔
      P.center ∈ S ∧
      G.edge (xs 0).val P.center ∧
      (∀ i, (xs (Fin.succ i)).val = P.tuple i) :=
  Iff.rfl

@[simp] theorem auxiliaryRootStructure_successors
    {V : Type u} [Fintype V] (G : Digraph V)
    (k : ℕ) (S : Set V) (xs : Fin 1 → RootsIn G k S) :
    (auxiliaryRootStructure G k S).func AuxiliaryFunc.successor xs =
      {r | G.Reaches (xs 0).val r.val} :=
  rfl

end AllThoseEPPA.Applications.KOrientations
