import AllThoseEPPA.Applications.KOrientations.AuxiliaryLanguage
import AllThoseEPPA.Applications.KOrientations.Closures

/-!
# Label reflection for root-only auxiliary partial maps

A crucial logical obligation of the two-stage EPPA application is
*reflection* of the labelled root relations, not just preservation
of positive tuples. The template pattern P may have its centre
outside the original input image, so it is not enough to check
only the old relation symbols.

If U is d-closed in the ambient graph, U ⊆ S and a tuple of roots
lies in U, an R_P or E_P relation on that tuple is positive
exactly when its centre lies in U and the defining root coordinates
(and incoming edge for E_P) agree. In particular no outside
pattern label can create a new positive relation after an
automorphism carries U onto another closed set.

This lemma does not assert that an arbitrary first-stage s-closed
copy S itself is d-closed.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

private theorem rootPattern_center_mem_of_closed_tuple
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (U : Set V) (hU : G.IsDClosed k U)
    {n : ℕ} (P : RootPattern G k n)
    (xs : Fin n → V)
    (hxs : ∀ i, xs i ∈ U)
    (hMatch : ∀ i, xs i = P.tuple i) :
    P.center ∈ U := by
  have htup : ∀ i, P.tuple i ∈ U := by
    intro i
    rw [← hMatch i]
    exact hxs i
  have hRoots : ∀ i, G.IsRoot k (P.tuple i) := by
    intro i
    have hi : P.tuple i ∈ G.roots k P.center := by
      rw [P.roots_eq]
      exact ⟨i, rfl⟩
    exact hi.1
  have hFiber : P.center ∈ G.dFiber k P.tuple :=
    ⟨P.positive, P.injective, hRoots, P.roots_eq⟩
  exact hU.2 n P.tuple htup hFiber

/-- On a root tuple in d-closed U⊆S, the full R_P predicate can
be tested by the centre's membership in U, rather than S.
Both directions are essential for auxiliary partial isomorphisms. -/
theorem auxiliary_root_label_iff_center_in_closed
    {V : Type u} [Fintype V]
    (G : Digraph V) (k n : ℕ)
    (S U : Set V) (hUS : U ⊆ S)
    (hU : G.IsDClosed k U)
    (P : RootPattern G k n)
    (xs : Fin n → RootsIn G k S)
    (hxs : ∀ i, (xs i).val ∈ U) :
    (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.root P) xs ↔
      P.center ∈ U ∧ ∀ i, (xs i).val = P.tuple i := by
  change (P.center ∈ S ∧ ∀ i, (xs i).val = P.tuple i) ↔
    (P.center ∈ U ∧ ∀ i, (xs i).val = P.tuple i)
  constructor
  · intro h
    exact ⟨rootPattern_center_mem_of_closed_tuple
      G k U hU P (fun i => (xs i).val) hxs h.2, h.2⟩
  · intro h
    exact ⟨hUS h.1, h.2⟩

/-- The analogous iff for incoming E_P relations includes its
directed root-to-centre edge, preserved by the first-stage
graph automorphism, and reflects labels from outside S too. -/
theorem auxiliary_incoming_label_iff_center_in_closed
    {V : Type u} [Fintype V]
    (G : Digraph V) (k n : ℕ)
    (S U : Set V) (hUS : U ⊆ S)
    (hU : G.IsDClosed k U)
    (P : RootPattern G k n)
    (xs : Fin (n + 1) → RootsIn G k S)
    (hxs : ∀ i, (xs i).val ∈ U) :
    (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.incoming P) xs ↔
      P.center ∈ U ∧ G.edge (xs 0).val P.center ∧
        (∀ i, (xs (Fin.succ i)).val = P.tuple i) := by
  change
    (P.center ∈ S ∧ G.edge (xs 0).val P.center ∧
      (∀ i, (xs (Fin.succ i)).val = P.tuple i)) ↔
    (P.center ∈ U ∧ G.edge (xs 0).val P.center ∧
      (∀ i, (xs (Fin.succ i)).val = P.tuple i))
  constructor
  · rintro ⟨_, he, ht⟩
    have hc : P.center ∈ U :=
      rootPattern_center_mem_of_closed_tuple
        G k U hU P
        (fun i => (xs (Fin.succ i)).val)
        (fun i => hxs (Fin.succ i)) ht
    exact ⟨hc, he, ht⟩
  · rintro ⟨hc, he, ht⟩
    exact ⟨hUS hc, he, ht⟩

end AllThoseEPPA.Applications.KOrientations
