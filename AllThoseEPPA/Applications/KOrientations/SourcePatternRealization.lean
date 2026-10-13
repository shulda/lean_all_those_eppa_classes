import AllThoseEPPA.Applications.KOrientations.RootPatternExistence

/-!
# Every root-pattern of a source vertex is realized in the root sort

A source set S that is successor-closed in the template graph
contains every reachable root of each of its elements.
Consequently the root-only auxiliary source realizes the complete
R_P relation of each root-pattern whose centre belongs to S.

This is an essential hypothesis for eventually proving that all
template outneighbours of a realized nonroot can be lifted to the
reconstruction: arbitrary S would not suffice.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- A successor-closed set of template vertices contains the
complete root set of each of its members. -/
theorem successorClosed_roots_subset
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S)
    {x : V} (hx : x ∈ S) :
    G.roots k x ⊆ S := by
  intro r hr
  exact hClosed x r hx hr.2

/-- The auxiliary source realizes the complete relation R_P for
any pattern centred in a successor-closed source S. -/
theorem auxiliarySource_realizes_rootPattern
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S)
    {n : ℕ} (P : RootPattern G k n)
    (hCenter : P.center ∈ S) :
    ∃ xs : Fin n → RootsIn G k S,
      (auxiliaryRootStructure G k S).rel (AuxiliaryRel.root P) xs := by
  have hRoot (i : Fin n) : P.tuple i ∈ G.roots k P.center := by
    rw [P.roots_eq]
    exact ⟨i, rfl⟩
  let xs : Fin n → RootsIn G k S :=
    fun i => ⟨P.tuple i,
      ⟨hClosed P.center (P.tuple i) hCenter (hRoot i).2,
       (hRoot i).1⟩⟩
  refine ⟨xs, ?_⟩
  exact (auxiliaryRootStructure_root G k n S P xs).2
    ⟨hCenter, fun _ => rfl⟩

/-- Existence of an R_P realization for an arbitrary nonroot in a
successor-closed source, assuming its reachable root set is nonempty. -/
theorem auxiliarySource_realizes_nonroot
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S)
    (x : V) (hx : x ∈ S)
    (hNotRoot : ¬ G.IsRoot k x)
    (hRoots : (G.roots k x).Nonempty) :
    ∃ (n : ℕ) (P : RootPattern G k n)
      (xs : Fin n → RootsIn G k S),
      P.center = x ∧
      (auxiliaryRootStructure G k S).rel (AuxiliaryRel.root P) xs := by
  obtain ⟨n, P, hc⟩ :=
    rootPattern_exists_of_nonroot_and_roots_nonempty
      G k x hNotRoot hRoots
  obtain ⟨xs, hRel⟩ :=
    auxiliarySource_realizes_rootPattern G k S hClosed P (by
      simpa only [hc] using hx)
  exact ⟨n, P, xs, hc, hRel⟩

end AllThoseEPPA.Applications.KOrientations
