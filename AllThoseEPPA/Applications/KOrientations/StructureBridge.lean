import AllThoseEPPA.Applications.KOrientations.Encoding
import AllThoseEPPA.Substructure

/-!
# Transfer of graph closure to the general EPPA \`Structure\` API

This module is the interface between the concrete \(k\)-orientation
development and the exact, set-valued function notion of substructure
in the already-checked \`AllThoseEPPA\` library.

In particular, the root-determined closure characterized in
\`ClosureMinimal\` is proved to be the library's *actual*
\`Structure.closureSet\` for \`dStructure G k\`, not merely an
unrelated helper set satisfying some closure properties.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- Closure in the unary successor structure is exactly closure under
directed reachability. -/
theorem successorStructure_isClosed_iff
    {V : Type u} (G : Digraph V) (S : Set V) :
    (successorStructure G).IsClosed S ↔
      ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S := by
  constructor
  · intro h x y hx hxy
    exact h SuccessorSymbol.successor
      (fun _ : Fin 1 => x) (fun _ => hx) hxy
  · intro h n F xs hxs v hv
    cases F with
    | successor =>
        exact h (xs 0) v (hxs 0) hv

/-- The library's exact d-substructure notion is equivalent to
closure under successors and every root-fibre operation. -/
theorem dStructure_isClosed_iff
    {V : Type u} [Fintype V] (G : Digraph V)
    (k : ℕ) (S : Set V) :
    (dStructure G k).IsClosed S ↔ G.IsDClosed k S := by
  constructor
  · intro h
    constructor
    · intro x y hx hxy
      exact h DFunctionSymbol.successor
        (fun _ : Fin 1 => x) (fun _ => hx) hxy
    · intro n xs hxs v hv
      have hpos : 0 < n := hv.1
      exact h (DFunctionSymbol.fiber n hpos) xs hxs hv
  · intro h n F xs hxs v hv
    cases F with
    | successor =>
        exact h.1 (xs 0) v (hxs 0) hv
    | fiber n _ =>
        exact h.2 n xs hxs hv

/-- The unary closure really is the closure operator of the paper's
unary-function language. -/
theorem successorClosure_eq_structureClosure
    {V : Type u} (G : Digraph V) (S : Set V) :
    G.successorClosure S = (successorStructure G).closureSet S := by
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨x, hxS, hxy⟩ := hy
    have hClosed :=
      (successorStructure_isClosed_iff G
        ((successorStructure G).closureSet S)).1
        ((successorStructure G).isClosed_closureSet S)
    exact hClosed x y
      ((successorStructure G).subset_closureSet S hxS) hxy
  · apply (successorStructure G).closureSet_minimal
      ((successorStructure_isClosed_iff G
        (G.successorClosure S)).2 (by
          intro x y hx hxy
          exact G.successorClosure_closed S hx hxy))
    exact G.subset_successorClosure S

/-- Exact root-determined closure formula, expressed in the
\`AllThoseEPPA.Structure.closureSet\` language.

The no-rootless-vertex hypothesis is used only in the direction
that enumerates a nonempty root set and applies an \(F_n\)-fibre. -/
theorem dGenerated_eq_structureClosure
    {V : Type u} [Fintype V] (G : Digraph V)
    (k : ℕ) (hRooted : G.HasReachableRoots k) (S : Set V) :
    G.dGenerated k S = (dStructure G k).closureSet S := by
  apply Set.Subset.antisymm
  · apply G.dGenerated_minimal k hRooted S
      ((dStructure G k).closureSet S)
    · exact (dStructure G k).subset_closureSet S
    · exact (dStructure_isClosed_iff G k
        ((dStructure G k).closureSet S)).1
        ((dStructure G k).isClosed_closureSet S)
  · apply (dStructure G k).closureSet_minimal
      ((dStructure_isClosed_iff G k
        (G.dGenerated k S)).2
        (G.dGenerated_isDClosed k S))
    exact G.subset_dGenerated k S

end AllThoseEPPA.Applications.KOrientations
