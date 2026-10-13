import AllThoseEPPA.Applications.KOrientations.AuxiliaryLanguage

/-!
# Root-pattern realizations are unary-closed in the original template

An R_P relation in the root-only auxiliary source lists **all**
roots reachable from the corresponding centre P.center. Because
reachable-root sets decrease along directed paths, each root r in
the tuple can only reach roots which are again in that tuple.

Thus the unordered tuple support forms an honest substructure of
the root-only auxiliary language: it is closed under its one
set-valued unary successor function. This is a local source lemma
needed to transport closed supports into a faithful B₁ witness.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- A realized R_P tuple in the original root-only auxiliary
structure is closed under all its unary function values. -/
theorem auxiliarySource_rootTuple_isClosed
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    {n : ℕ} (P : RootPattern G k n)
    (xs : Fin n → RootsIn G k S)
    (hRel : (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.root P) xs) :
    (auxiliaryRootStructure G k S).IsClosed (Set.range xs) := by
  have hCoords : ∀ i, (xs i).val = P.tuple i :=
    ((auxiliaryRootStructure_root G k n S P xs).mp hRel).2
  intro ar F ys hys z hz
  cases F with
  | successor =>
      obtain ⟨i, hi⟩ := hys 0
      have hStep : G.Reaches (xs i).val z.val := by
        change G.Reaches (ys 0).val z.val at hz
        simpa only [← hi] using hz
      have hxroot : (xs i).val ∈ G.roots k P.center := by
        rw [P.roots_eq]
        exact ⟨i, (hCoords i).symm⟩
      have hzroot : z.val ∈ G.roots k P.center :=
        ⟨z.property.2, G.reaches_trans hxroot.2 hStep⟩
      rw [P.roots_eq] at hzroot
      obtain ⟨j, hj⟩ := hzroot
      refine ⟨j, ?_⟩
      apply Subtype.ext
      calc
        (xs j).val = P.tuple j := hCoords j
        _ = z.val := hj

end AllThoseEPPA.Applications.KOrientations
