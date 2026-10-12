import AllThoseEPPA.Applications.KOrientations.StructureBridge

/-!
# Closed d-substructures are determined by their root traces

This module strengthens the root-determined closure theorem to the
precise criterion for an arbitrary substructure:

  T is d-closed ↔ ∀ v, v ∈ T ↔ roots(v) ⊆ T.

Under the no-rootless-vertices hypothesis, two d-closed sets with the
same roots are equal. The statement is about the *actual* set-valued
function structure, via the bridge proved in StructureBridge.lean.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

namespace Digraph

variable {V : Type u} [Fintype V] (G : Digraph V)

/-- Every root reachable from a vertex of a d-closed set lies in it. -/
theorem roots_subset_of_mem_isDClosed (k : ℕ)
    {S : Set V} (hClosed : G.IsDClosed k S)
    {v : V} (hv : v ∈ S) :
    G.roots k v ⊆ S := by
  intro r hr
  exact hClosed.1 v r hv hr.2

/-- The converse needs nonempty root sets: a vertex is recovered by
the d-fibre indexed by all of its reachable roots. -/
theorem mem_of_roots_subset_isDClosed (k : ℕ)
    (hRooted : G.HasReachableRoots k)
    {S : Set V} (hClosed : G.IsDClosed k S)
    {v : V} (hRoots : G.roots k v ⊆ S) :
    v ∈ S := by
  have hv : v ∈ G.dGenerated k S := by
    intro r hr
    exact ⟨r, hRoots hr, G.reaches_refl r⟩
  exact G.dGenerated_minimal k hRooted S S
    Set.Subset.rfl hClosed hv

/-- The complete root-saturation characterization of d-closed sets. -/
theorem isDClosed_iff_rootSaturated (k : ℕ)
    (hRooted : G.HasReachableRoots k) (S : Set V) :
    G.IsDClosed k S ↔
      ∀ v : V, v ∈ S ↔ G.roots k v ⊆ S := by
  constructor
  · intro hClosed v
    exact ⟨G.roots_subset_of_mem_isDClosed k hClosed,
      G.mem_of_roots_subset_isDClosed k hRooted hClosed⟩
  · intro h
    constructor
    · intro x y hx hxy
      apply (h y).2
      intro r hr
      exact (h x).1 hx (G.roots_antitone k hxy hr)
    · intro n xs hxs v hv
      apply (h v).2
      intro r hr
      rw [G.roots_eq_range_of_mem_dFiber k hv] at hr
      rcases hr with ⟨i, rfl⟩
      exact hxs i

/-- The root-saturation test, now stated in the general EPPA
library's exact closed-substructure predicate. -/
theorem dStructure_isClosed_iff_rootSaturated (k : ℕ)
    (hRooted : G.HasReachableRoots k) (S : Set V) :
    (dStructure G k).IsClosed S ↔
      ∀ v : V, v ∈ S ↔ G.roots k v ⊆ S := by
  exact (dStructure_isClosed_iff G k S).trans
    (G.isDClosed_iff_rootSaturated k hRooted S)

/-- Two d-closed induced substructures are identical as soon as they
contain the same roots. This is the exact-domain criterion used in
the manuscript's canonical reconstruction. -/
theorem eq_of_isDClosed_of_same_roots (k : ℕ)
    (hRooted : G.HasReachableRoots k)
    {S T : Set V}
    (hS : G.IsDClosed k S)
    (hT : G.IsDClosed k T)
    (hRoots : ∀ r : V, G.IsRoot k r → (r ∈ S ↔ r ∈ T)) :
    S = T := by
  have hs := (G.isDClosed_iff_rootSaturated k hRooted S).mp hS
  have ht := (G.isDClosed_iff_rootSaturated k hRooted T).mp hT
  ext v
  constructor
  · intro hv
    apply (ht v).2
    intro r hr
    exact (hRoots r hr.1).mp ((hs v).1 hv hr)
  · intro hv
    apply (hs v).2
    intro r hr
    exact (hRoots r hr.1).mpr ((ht v).1 hv hr)

end Digraph

end AllThoseEPPA.Applications.KOrientations
