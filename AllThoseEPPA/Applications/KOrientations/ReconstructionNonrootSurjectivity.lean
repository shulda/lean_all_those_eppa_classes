import AllThoseEPPA.Applications.KOrientations.SecondStageNestedPatternLift
import AllThoseEPPA.Applications.KOrientations.ReconstructionNonrootOutdegree
import AllThoseEPPA.Applications.KOrientations.ReconstructionRootNeighbourCorrespondence

/-!
# Surjectivity of the reconstructed nonroot neighbourhood projection

Earlier we injected all neighbours of a canonical nonroot p=(x,W)
into the original outneighbours of x in B₀. To prove the exact
outdegree k (and hence that p is genuinely a nonroot in the final
graph), the projection must also be surjective.

This requires genuinely mathematical hypotheses: the distinguished
source S must be successor-closed and every vertex of S must reach
some root. We do NOT assume B₀ itself is rooted.

For a template root target y, the canonical matching produces the
outgoing B₁-root target. For a nonroot target y, a common faithful
move of the realized R_P tuple shows that y still has nonempty
reachable roots, then the nested-pattern lift constructs a realized
R_Q tuple supported inside W. This gives the desired outgoing
canonical nonroot over y.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every outgoing neighbour of a realized nonroot has some
reachable root, provided the source is rooted and successor-closed.
This is a local statement: the entire ambient B₀ need not be rooted. -/
theorem faithful_realized_nonroot_successor_has_roots
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S)
    (hRootedS : ∀ x : V, x ∈ S → (G.roots k x).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p : CanonicalNonroot G k B)
    {y : V} (hEdge : G.edge p.center y) :
    (G.roots k y).Nonempty := by
  classical
  obtain ⟨n, P, xs, hc, hRel, _⟩ := p.witnessed
  obtain ⟨f, ts, _, hSrc⟩ :=
    faithful_auxiliary_relation_movable G k S B ι hFaith
      (AuxiliaryRel.root P) xs hRel
  let g : G.graphAut := ι.lang⁻¹ * f.lang
  have hPcenter : g.1 P.center ∈ S := by
    exact ((auxiliaryRootStructure_root G k n S
      (RootPattern.transportAut g P) ts).mp hSrc).1
  have hEdgeMoved : G.edge (g.1 P.center) (g.1 y) :=
    (g.2 P.center y).2 (by simpa only [hc] using hEdge)
  have hYinS : g.1 y ∈ S :=
    hClosed (g.1 P.center) (g.1 y) hPcenter
      (G.reaches_of_edge hEdgeMoved)
  have hGY : (G.roots k (g.1 y)).Nonempty :=
    hRootedS (g.1 y) hYinS
  rw [G.graphAut_roots_image k g y] at hGY
  obtain ⟨z, ⟨r, hr, _⟩⟩ := hGY
  exact ⟨r, hr⟩

/-- For any outgoing template neighbour y of a realized nonroot
p=(x,W), there exists a corresponding outgoing reconstructed
neighbour over y, under successor-closed rooted source assumptions.
Thus the already verified neighbourhood projection is surjective. -/
theorem reconstructedNonrootNeighbourProjection_surjective
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S)
    (hRootedS : ∀ x : V, x ∈ S → (G.roots k x).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p : CanonicalNonroot G k B) :
    Function.Surjective (reconstructedNonrootNeighbourProjection G k B p) := by
  classical
  intro target
  let y : V := target.val
  have hy : G.edge p.center y :=
    (G.mem_outNeighbors p.center y).1 target.property
  by_cases hRoot : G.IsRoot k y
  · obtain ⟨w, _, hMatch⟩ :=
      reconstructedRootNeighbour_exists G k B p hRoot hy
    have hMatchEdge : ∃ r : V,
        G.edge p.center r ∧ RootMatches G k B p r w :=
      ⟨y, hy, hMatch⟩
    let z : {t : ReconstructedCarrier G k B //
        ReconstructedEdge G k B (.inr p) t} :=
      ⟨.inl w, hMatchEdge⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change Classical.choose hMatchEdge = y
    have hSelected : RootMatches G k B p
        (Classical.choose hMatchEdge) w :=
      (Classical.choose_spec hMatchEdge).2
    exact RootMatches.left_unique p S ι hFaith hSelected hMatch
  · have hRoots : (G.roots k y).Nonempty :=
      faithful_realized_nonroot_successor_has_roots
        G k S hClosed hRootedS B ι hFaith p hy
    obtain ⟨m, Q, hQc⟩ :=
      rootPattern_exists_of_nonroot_and_roots_nonempty
        G k y hRoot hRoots
    obtain ⟨n, P, xs, hc, hRel, hU⟩ := p.witnessed
    have hPQ : G.edge P.center Q.center := by
      simpa only [hc, hQc] using hy
    obtain ⟨ys, hQrel, hSubset⟩ :=
      faithful_auxiliary_lift_nested_rootPattern
        G k S hClosed B ι hFaith P Q hPQ xs hRel
    let q : CanonicalNonroot G k B :=
      CanonicalNonroot.ofRelation Q ys hQrel
    have hqCenter : q.center = y := hQc
    have hqSub : q.support ⊆ p.support := by
      simpa only [q, CanonicalNonroot.ofRelation_support, ← hU]
        using hSubset
    have hEdgeQ : ReconstructedEdge G k B (.inr p) (.inr q) :=
      ⟨by simpa only [hqCenter] using hy, hqSub⟩
    refine ⟨⟨.inr q, hEdgeQ⟩, ?_⟩
    apply Subtype.ext
    change q.center = y
    exact hqCenter

end AllThoseEPPA.Applications.KOrientations
