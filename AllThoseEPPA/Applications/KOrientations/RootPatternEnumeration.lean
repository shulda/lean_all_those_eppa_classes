import AllThoseEPPA.Applications.KOrientations.AuxiliaryLanguage
import Mathlib.Data.Fintype.EquivFin

/-!
# Enumerating every nonempty finite reachable-root set

The auxiliary language labels are genuine RootPattern objects:
a centre x, a positive-length injective ordered enumeration
of *all* roots reachable from x, and a proof that x is not
itself a root.

Every finite non-root with a nonempty reachable-root set has
such a label. This lemma is indispensable when reconstructing
a non-root successor of a labelled vertex and later proving
surjectivity of the neighbourhood correspondence; B₀ itself
need not have roots reachable from every vertex.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- Any finite non-root with at least one reachable root admits
a complete root-pattern label in the auxiliary language. -/
theorem exists_rootPattern_of_nonempty_roots
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (x : V)
    (hNonroot : ¬ G.IsRoot k x)
    (hRoots : (G.roots k x).Nonempty) :
    ∃ (n : ℕ) (P : RootPattern G k n), P.center = x := by
  classical
  let n : ℕ := Fintype.card (G.roots k x)
  let e : Fin n ≃ G.roots k x :=
    (Fintype.equivFin (G.roots k x)).symm
  have hpositive : 0 < n := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨r,hr⟩ := hRoots
    exact ⟨⟨r,hr⟩⟩
  let P : RootPattern G k n :=
    { center := x
      nonroot := hNonroot
      positive := hpositive
      tuple := fun i => (e i).val
      injective := by
        intro i j hij
        apply e.injective
        apply Subtype.ext
        exact hij
      roots_eq := by
        ext z
        constructor
        · intro hz
          obtain ⟨i,hi⟩ := e.surjective ⟨z,hz⟩
          exact ⟨i,congrArg Subtype.val hi⟩
        · rintro ⟨i,rfl⟩
          exact (e i).property }
  exact ⟨n,P,rfl⟩

end AllThoseEPPA.Applications.KOrientations
