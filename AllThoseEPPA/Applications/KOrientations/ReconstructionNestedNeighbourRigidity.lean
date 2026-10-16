import AllThoseEPPA.Applications.KOrientations.ReconstructionEdges

/-!
# Nested supports rigidly determine reconstructed non-root neighbours

For realized labels with support Z ⊆ W, the second-stage faithful
witness identifies exactly the same template root with the same
realized coordinate in both supports. Therefore the intrinsic matching
of a smaller support is the restriction of that of the larger support.

A key consequence: for a fixed canonical non-root (x,W), there is
*at most one* outgoing non-root neighbour (y,Z) over each template
centre y. This is a crucial fibre-injectivity ingredient of the
eventual outdegree bound, and is independent of graph-root status
and final d-closure membership.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every matching in a smaller canonical non-root support is also
a matching in the larger support, with the same template root and
the same realized root point. The template centres may differ. -/
theorem rootMatches_of_nested_support
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p q : CanonicalNonroot G k B)
    (hsub : q.support ⊆ p.support)
    {r : V} {w : W}
    (h : RootMatches G k B q r w) :
    RootMatches G k B p r w := by
  obtain ⟨n, P, xs, hc, hP, hU⟩ := p.witnessed
  obtain ⟨m, Q, ys, j, _, hQ, hZ, hr, hw⟩ := h
  have hwP : w ∈ Set.range xs := by
    rw [hU]
    exact hsub (by rw [← hZ]; exact ⟨j, hw⟩)
  obtain ⟨i, hi⟩ := hwP
  have hNested : Set.range ys ⊆ Set.range xs := by
    rw [hZ, hU]
    exact hsub
  have hCoord : xs i = ys j := hi.trans hw.symm
  have hRoot :
      P.tuple i = Q.tuple j :=
    (faithful_auxiliary_nestedSupport_coordinateEq
      G k S B ι hFaith P Q xs ys hP hQ hNested i j).mpr hCoord
  exact ⟨n, P, xs, i, hc, hP, hU, hRoot.trans hr, hi⟩

/-- If two realized smaller supports lie in W and have the same
template centre, each support is contained in the other. -/
theorem reconstructed_nested_support_subset_of_same_center
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p q t : CanonicalNonroot G k B)
    (hq : q.support ⊆ p.support)
    (ht : t.support ⊆ p.support)
    (hc : q.center = t.center) :
    q.support ⊆ t.support := by
  intro w hw
  obtain ⟨r, hqr⟩ := RootMatches.exists_of_support q hw
  have hpr : RootMatches G k B p r w :=
    rootMatches_of_nested_support G k S B ι hFaith p q hq hqr
  have hrt : r ∈ G.roots k t.center := by
    have hrq := RootMatches.root_mem q hqr
    simpa only [hc] using hrq
  obtain ⟨z, htz⟩ := RootMatches.exists_of_root t hrt
  have hpz : RootMatches G k B p r z :=
    rootMatches_of_nested_support G k S B ι hFaith p t ht htz
  have hwz : w = z :=
    RootMatches.right_unique p S ι hFaith hpr hpz
  exact hwz ▸ RootMatches.support_mem t htz

/-- Each template centre has at most one realized smaller support
inside a fixed canonical non-root support W. -/
theorem reconstructed_nested_support_unique_of_same_center
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p q t : CanonicalNonroot G k B)
    (hq : q.support ⊆ p.support)
    (ht : t.support ⊆ p.support)
    (hc : q.center = t.center) :
    q = t := by
  apply CanonicalNonroot.eq_of_center_support q t hc
  apply Set.Subset.antisymm
  · exact reconstructed_nested_support_subset_of_same_center
      G k S B ι hFaith p q t hq ht hc
  · exact reconstructed_nested_support_subset_of_same_center
      G k S B ι hFaith p t q ht hq hc.symm

/-- In the fourth reconstructed edge case, the centre projection
is injective on the outgoing non-root neighbours of a fixed p. -/
theorem reconstructed_nonroot_neighbour_unique_of_center
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p q t : CanonicalNonroot G k B)
    (hq : ReconstructedEdge G k B (.inr p) (.inr q))
    (ht : ReconstructedEdge G k B (.inr p) (.inr t))
    (hc : q.center = t.center) :
    q = t :=
  reconstructed_nested_support_unique_of_same_center
    G k S B ι hFaith p q t hq.2 ht.2 hc

end AllThoseEPPA.Applications.KOrientations
