import AllThoseEPPA.Applications.KOrientations.AuxiliaryLanguage
import Mathlib.Data.Fintype.EquivFin

/-!
# Construct an actual root-pattern label from a nonempty root set

The auxiliary language has a relation R_P for *every* non-root
template vertex whose complete set of reachable roots is nonempty.
To use such a relation in a future neighbourhood-surjectivity proof,
we need the constructor: enumerate a finite nonempty root set,
not merely assert that a suitable P exists.

This lemma does not assume any ambient successor-closed source set S.
A separate construction will show the generated label is realized
inside S whenever its centre belongs to S and S is successor-closed.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- Every template nonroot with nonempty root set has at least one
admissible auxiliary-language root-pattern label. The enumeration is
chosen noncomputably from the finite root subset. -/
theorem rootPattern_exists_of_nonroot_and_roots_nonempty
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (x : V)
    (hNonroot : ¬ G.IsRoot k x)
    (hNonempty : (G.roots k x).Nonempty) :
    ∃ (n : ℕ) (P : RootPattern G k n), P.center = x := by
  classical
  let R : Type u := G.roots k x
  let n := Fintype.card R
  let e : Fin n ≃ R := (Fintype.equivFin R).symm
  have hR : Nonempty R := by
    obtain ⟨r, hr⟩ := hNonempty
    exact ⟨⟨r, hr⟩⟩
  have hn : 0 < n := Fintype.card_pos_iff.mpr hR
  let P : RootPattern G k n :=
    { center := x
      nonroot := hNonroot
      positive := hn
      tuple := fun i => (e i).val
      injective := by
        intro i j hij
        apply e.injective
        apply Subtype.ext
        exact hij
      roots_eq := by
        ext r
        constructor
        · intro hr
          obtain ⟨i, hi⟩ := e.surjective (⟨r, hr⟩ : R)
          exact ⟨i, congrArg Subtype.val hi⟩
        · rintro ⟨i, rfl⟩
          exact (e i).property }
  exact ⟨n, P, rfl⟩

end AllThoseEPPA.Applications.KOrientations
