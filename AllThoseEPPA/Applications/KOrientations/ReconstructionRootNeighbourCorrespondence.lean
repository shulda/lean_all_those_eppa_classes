import AllThoseEPPA.Applications.KOrientations.ReconstructionEdges
import AllThoseEPPA.Applications.KOrientations.RootMatchingEquiv

/-!
# Exact root targets of reconstructed non-root vertices

For p=(x,W), the outgoing edges p→w to the B₁-root sort are exactly
the original template edges x→r, with r a root, transported by the
canonical matching eta. The relation-level proof deliberately avoids
a preferred representative of R_P and exposes both existence and
uniqueness of the matched outgoing root.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every original edge from the template centre to a root has
a corresponding outgoing reconstructed edge into B₁'s root sort. -/
theorem reconstructedRootNeighbour_exists
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (p : CanonicalNonroot G k B)
    {r : V} (hRoot : G.IsRoot k r) (hEdge : G.edge p.center r) :
    ∃ w : W, ReconstructedEdge G k B (.inr p) (.inl w) ∧
      RootMatches G k B p r w := by
  have hr : r ∈ G.roots k p.center :=
    ⟨hRoot, G.reaches_of_edge hEdge⟩
  obtain ⟨w, hMatch⟩ := RootMatches.exists_of_root p hr
  exact ⟨w, ⟨r, hEdge, hMatch⟩, hMatch⟩

/-- For a fixed template root target r, that reconstructed root target
is unique whenever B₁ is irreducible-structure faithful. -/
theorem reconstructedRootNeighbour_existsUnique
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p : CanonicalNonroot G k B)
    {r : V} (hRoot : G.IsRoot k r) (hEdge : G.edge p.center r) :
    ∃! w : W, ReconstructedEdge G k B (.inr p) (.inl w) ∧
      RootMatches G k B p r w := by
  obtain ⟨w, hwedge, hwmatch⟩ :=
    reconstructedRootNeighbour_exists G k B p hRoot hEdge
  refine ⟨w, ⟨hwedge, hwmatch⟩, ?_⟩
  intro z hz
  exact RootMatches.right_unique p S ι hFaith hwmatch hz.2

/-- On any matched pair r↔w, the reconstructed edge p→w holds
if and only if the original template edge x→r holds. -/
theorem reconstructedRootNeighbour_iff_templateEdge
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p : CanonicalNonroot G k B)
    {r : V} {w : W} (hMatch : RootMatches G k B p r w) :
    ReconstructedEdge G k B (.inr p) (.inl w) ↔
      G.edge p.center r := by
  constructor
  · rintro ⟨s, hEdge, hMatchS⟩
    have hs : s = r :=
      RootMatches.left_unique p S ι hFaith hMatchS hMatch
    simpa only [hs] using hEdge
  · intro hEdge
    exact ⟨r, hEdge, hMatch⟩

end AllThoseEPPA.Applications.KOrientations
