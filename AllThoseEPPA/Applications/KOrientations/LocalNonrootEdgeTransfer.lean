import AllThoseEPPA.Applications.KOrientations.CommonMoveRootRigidity
import AllThoseEPPA.Applications.KOrientations.ReconstructionEdges

/-!
# Local edge reflection for two reconstructed nonroots

The C4 edge clause says that p=(x,W) points to q=(y,Z) exactly when
x→y in the B₀ template AND Z⊆W. Under one fixed B₁ automorphism f
which sends both supports into the old root sort, the second
condition follows automatically from the first.

Indeed an edge x→y implies roots(y)⊆roots(x); every root of q has a
corresponding root of p, and common-move rigidity forces their
B₁ coordinates to coincide. This is the nonroot/nonroot case of
local edge preservation *and reflection* (Claim P2) without any
arbitrary quotient representatives.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- If both supports can be moved by one f into the source and the
template centres form a directed edge, then q.support⊆p.support. -/
theorem commonMove_nonroot_edge_support_subset
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p q : CanonicalNonroot G k B)
    (hp : ∀ w ∈ p.support,
      ∃ t : RootsIn G k S, f w = ι t)
    (hq : ∀ w ∈ q.support,
      ∃ t : RootsIn G k S, f w = ι t)
    (hEdge : G.edge p.center q.center) :
    q.support ⊆ p.support := by
  intro w hw
  obtain ⟨r, hqr⟩ := RootMatches.exists_of_support q hw
  have hrp : r ∈ G.roots k p.center :=
    G.roots_antitone_edge k hEdge (RootMatches.root_mem q hqr)
  obtain ⟨z, hpz⟩ := RootMatches.exists_of_root p hrp
  have hzw : z = w :=
    rootMatches_eq_of_common_move G k S B ι f
      p q hp hq hpz hqr
  rw [← hzw]
  exact RootMatches.support_mem p hpz

/-- Exact graph edge equivalence for two support-moved nonroots,
with the actual B₀ graph-automorphism language correction. -/
theorem local_nonroot_nonroot_edge_iff
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p q : CanonicalNonroot G k B)
    (hp : ∀ w ∈ p.support,
      ∃ t : RootsIn G k S, f w = ι t)
    (hq : ∀ w ∈ q.support,
      ∃ t : RootsIn G k S, f w = ι t) :
    ReconstructedEdge G k B (.inr p) (.inr q) ↔
      G.edge
        ((ι.lang⁻¹ * f.lang : G.graphAut).1 p.center)
        ((ι.lang⁻¹ * f.lang : G.graphAut).1 q.center) := by
  let g : G.graphAut := ι.lang⁻¹ * f.lang
  constructor
  · intro h
    exact (g.2 p.center q.center).2 h.1
  · intro h
    have hOriginal : G.edge p.center q.center :=
      (g.2 p.center q.center).1 h
    exact ⟨hOriginal,
      commonMove_nonroot_edge_support_subset
        G k S B ι f p q hp hq hOriginal⟩

end AllThoseEPPA.Applications.KOrientations
