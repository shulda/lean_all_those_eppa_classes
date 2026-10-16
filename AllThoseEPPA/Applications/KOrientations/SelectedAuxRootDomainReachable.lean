import AllThoseEPPA.Applications.KOrientations.FirstStageSelectedAuxRootPartialAutomorphism
import AllThoseEPPA.Applications.KOrientations.EmbeddedSuccessorSourceRooted
import AllThoseEPPA.Applications.KOrientations.StructureBridge

/-!
# All reachable roots of an original d-partial domain lie in the selected Γ-root domain

The actual first-stage successor embedding ι:A→B₀ has a source
image S closed under every directed successor. A root of B₀
reachable from an embedded old point ι(x) is therefore not an
arbitrary new root: exact successor-fibre preservation lifts it
back to an actual old successor y of x.

If x lies in the source of a full d(A) partial automorphism p,
that source is genuinely CLOSED under the set-valued unary
successor. Thus every such y belongs to p.source. The
corresponding root in the selected second auxiliary Γ-source
belongs to the exact induced closed Γ-root partial-map domain.

This is the geometric domain-support inclusion needed to use
the real second coherent selected B₁ extension on EVERY root
supporting an original source nonroot, not merely on a single
chosen root. No global g[S]=S, no ambient full d-closure of S,
and no unproved higher-arity collapse is used.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The selected full Γ-root partial automorphism really acts
on ALL ambient B₀ reachable roots of any original full-d
partial source vertex, with exact original d-closure and
successor embedding image transport. -/
theorem firstStage_selectedAuxRootDomain_contains_sourceRoots
    {V : Type u} {W : Type v}
    [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (x : V) (hx : x ∈ p.source)
    (r : RootsIn G k (Set.range ι.toFun))
    (hr : r.val ∈ G.roots k (ι x)) :
    r ∈ (firstStage_selectedAuxRootPartialAutomorphism A G k ι s p).source := by
  have hReach : r.val ∈ G.successors (ι x) := hr.2
  have hImage : r.val ∈ Structure.imageSet ι.toFun (A.successors x) := by
    rw [successorEmbedding_successors_image A G ι x]
    exact hReach
  obtain ⟨y, hyReach, hry⟩ := hImage
  have hySource : y ∈ p.source :=
    ((dStructure_isClosed_iff A k p.source).1 p.source_closed).1
      x y hx hyReach
  change (⟨r.val, r.property.1⟩ : Set.range ι.toFun) ∈
    (firstStageFullDSourceEmbedding A G k ι).toFun '' p.source
  refine ⟨y, hySource, ?_⟩
  apply Subtype.ext
  exact hry

end AllThoseEPPA.Applications.KOrientations
