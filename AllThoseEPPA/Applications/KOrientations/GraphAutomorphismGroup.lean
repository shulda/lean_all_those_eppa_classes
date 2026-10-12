import AllThoseEPPA.Applications.KOrientations.GraphPermutations
import Mathlib.Data.Fintype.Perm

/-!
# Finite graph-automorphism group as the auxiliary language action group

The auxiliary language may be acted on by the *whole* automorphism
group of the finite template; the public EPPA API does not require a
faithful symbol action. This avoids lifting from the quotient of
automorphisms acting on indexed relation symbols.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

namespace Digraph

variable {V : Type u} [Fintype V] (G : Digraph V)

/-- Graph automorphisms form a subgroup of the permutation group. -/
def graphAut : Subgroup (Equiv.Perm V) where
  carrier := {g | ∀ x y, G.edge (g x) (g y) ↔ G.edge x y}
  one_mem' := by
    intro x y
    exact Iff.rfl
  mul_mem' := by
    intro g h hg hh x y
    change G.edge (g (h x)) (g (h y)) ↔ G.edge x y
    exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    change G.edge (g.symm x) (g.symm y) ↔ G.edge x y
    have h := hg (g.symm x) (g.symm y)
    simpa only [g.apply_symm_apply] using h.symm

/-- Finite vertex set implies finite automorphism group. -/
instance graphAut_finite : Finite G.graphAut := by
  classical
  exact Finite.of_injective
    (fun g : G.graphAut => (g : Equiv.Perm V))
    Subtype.val_injective

/-- Root status is invariant under any element of the graph group. -/
theorem graphAut_root_iff (k : ℕ) (g : G.graphAut) (x : V) :
    G.IsRoot k (g.1 x) ↔ G.IsRoot k x :=
  G.isRoot_iff_perm k g.1 g.2 x

/-- The group action is equivariant on each complete root set. -/
theorem graphAut_roots_image (k : ℕ) (g : G.graphAut) (x : V) :
    G.roots k (g.1 x) = g.1 '' G.roots k x :=
  G.roots_image_of_perm k g.1 g.2 x

end Digraph
end AllThoseEPPA.Applications.KOrientations
