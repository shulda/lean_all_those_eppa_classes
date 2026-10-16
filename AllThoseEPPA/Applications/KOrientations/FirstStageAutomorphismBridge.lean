import AllThoseEPPA.Applications.KOrientations.FirstStageInClass
import AllThoseEPPA.Applications.KOrientations.GraphAutomorphismGroup
import AllThoseEPPA.Automorphism
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# From successor-language automorphisms to graph automorphisms

The first-stage coherent EPPA witness yields automorphisms of its
successor expansion, while the second-stage auxiliary language uses
the full graph automorphism group. This bridge retains the actual
vertex permutation and the correct composition order.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- A total automorphism of a canonical successor structure induces
an element of its oriented graph automorphism subgroup. -/
noncomputable def graphAutOfSuccessorAut
    {V : Type u} [Fintype V] (G : Digraph V)
    (f : Structure.Automorphism successorAction (successorStructure G)) :
    G.graphAut := by
  classical
  refine ⟨f.toEquiv, ?_⟩
  intro x y
  have h := Structure.Automorphism.map_rel_iff
    f EdgeSymbol.edge ![x, y]
  have htuple : (f ∘ ![x, y]) = ![f x, f y] := by
    funext i
    fin_cases i <;> rfl
  rw [htuple] at h
  change G.edge (f x) (f y) ↔ G.edge x y at h
  exact h

@[simp] theorem graphAutOfSuccessorAut_apply
    {V : Type u} [Fintype V] (G : Digraph V)
    (f : Structure.Automorphism successorAction (successorStructure G))
    (x : V) :
    (graphAutOfSuccessorAut G f).1 x = f x := rfl

/-- The graph automorphism subgroup product has the same composition
order as the first-stage coherent EPPA extensions. -/
theorem graphAutOfSuccessorAut_comp
    {V : Type u} [Fintype V] (G : Digraph V)
    (f g : Structure.Automorphism successorAction (successorStructure G)) :
    graphAutOfSuccessorAut G (f.comp g) =
      graphAutOfSuccessorAut G f * graphAutOfSuccessorAut G g := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (f.comp g) x = f (g x)
  exact Structure.Automorphism.comp_apply f g x

end AllThoseEPPA.Applications.KOrientations
