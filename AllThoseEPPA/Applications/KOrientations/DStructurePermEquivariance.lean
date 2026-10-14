import AllThoseEPPA.Applications.KOrientations.GraphPermutations
import AllThoseEPPA.Applications.KOrientations.Encoding

/-!
# Exact equivariance of the full d-language

The d-structure is canonically defined by directed edges, reachable
successors and all finite root fibres. Consequently every permutation
of the vertex sort preserving and reflecting edges also preserves and
reflects *every* symbol of the full d-language.

This is a uniform arity-independent transport lemma, including all
positive-arity set-valued fibre functions. It is useful when the actual
second-stage automorphism group acts on the reconstructed carrier:
no additional lift or finite root-arity bound is required.

The module establishes exact set transport and does not conflate this
result with the still-open EPPA extension/gluing assertion.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

namespace Digraph

/-- Exact invariance of every d-fibre membership predicate under
a graph automorphism. No rootedness assumption is necessary. -/
theorem dFiber_perm_iff
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (g : Equiv.Perm V)
    (hEdge : ∀ x y, G.edge (g x) (g y) ↔ G.edge x y)
    {n : ℕ} (xs : Fin n → V) (z : V) :
    g z ∈ G.dFiber k (g ∘ xs) ↔ z ∈ G.dFiber k xs := by
  change
    (0 < n ∧ Function.Injective (g ∘ xs) ∧
      (∀ i, G.IsRoot k (g (xs i))) ∧
      G.roots k (g z) = Set.range (g ∘ xs)) ↔
    (0 < n ∧ Function.Injective xs ∧
      (∀ i, G.IsRoot k (xs i)) ∧
      G.roots k z = Set.range xs)
  rw [G.roots_image_of_perm k g hEdge z, Set.range_comp]
  constructor
  · rintro ⟨hn, hi, hr, hs⟩
    refine ⟨hn, ?_, ?_, ?_⟩
    · intro i j hij
      exact hi (congrArg g hij)
    · intro i
      exact (G.isRoot_iff_perm k g hEdge (xs i)).mp (hr i)
    · exact (Set.image_injective.mpr g.injective) hs
  · rintro ⟨hn, hi, hr, hs⟩
    refine ⟨hn, ?_, ?_, ?_⟩
    · intro i j hij
      exact hi (g.injective hij)
    · intro i
      exact (G.isRoot_iff_perm k g hEdge (xs i)).mpr (hr i)
    · exact congrArg (fun T : Set V => g '' T) hs

end Digraph

/-- All directed-edge relation symbols of the d-structure are
preserved and reflected by a graph permutation. -/
theorem dStructure_rel_perm_iff
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (g : Equiv.Perm V)
    (hEdge : ∀ x y, G.edge (g x) (g y) ↔ G.edge x y)
    {n : ℕ} (R : EdgeSymbol n) (xs : Fin n → V) :
    (dStructure G k).rel R (g ∘ xs) ↔
      (dStructure G k).rel R xs := by
  cases R with
  | edge =>
      change G.edge (g (xs 0)) (g (xs 1)) ↔
        G.edge (xs 0) (xs 1)
      exact hEdge (xs 0) (xs 1)

/-- Every set-valued function of the d-language commutes *exactly*
with a graph permutation, including successor and all root-fibre
symbols of arbitrary positive arity. -/
theorem dStructure_func_image_perm
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (g : Equiv.Perm V)
    (hEdge : ∀ x y, G.edge (g x) (g y) ↔ G.edge x y)
    {n : ℕ} (F : DFunctionSymbol n) (xs : Fin n → V) :
    g '' (dStructure G k).func F xs =
      (dStructure G k).func F (g ∘ xs) := by
  cases F with
  | successor =>
      change g '' G.successors (xs 0) =
        G.successors (g (xs 0))
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (G.reaches_iff_perm g hEdge).mpr hx
      · intro hy
        refine ⟨g.symm y, ?_, g.apply_symm_apply y⟩
        apply (G.reaches_iff_perm g hEdge).mp
        change G.Reaches (g (xs 0)) y at hy
        simpa only [g.apply_symm_apply] using hy
  | fiber n hpos =>
      change g '' G.dFiber k xs = G.dFiber k (g ∘ xs)
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (G.dFiber_perm_iff k g hEdge xs x).mpr hx
      · intro hy
        refine ⟨g.symm y, ?_, g.apply_symm_apply y⟩
        apply (G.dFiber_perm_iff k g hEdge xs (g.symm y)).mp
        simpa only [g.apply_symm_apply] using hy

end AllThoseEPPA.Applications.KOrientations
