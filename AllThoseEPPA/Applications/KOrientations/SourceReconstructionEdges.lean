import AllThoseEPPA.Applications.KOrientations.SourceReconstructionNonroot
import AllThoseEPPA.Applications.KOrientations.ReconstructionEdges
import AllThoseEPPA.Applications.KOrientations.SecondStageRootDigraph
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# All four source-edge cases lift to the reconstructed graph

Let ι₁ be the actual embedding of the root-only source into the
second-stage faithful witness. Every source nonroot is reconstructed
from a witnessed R_P tuple. Its template centre is transformed by
ι₁.lang; its root tuple is transformed by ι₁.toFun.

Every template source edge lifts under these maps:
* root → root: preservation of the binary edge symbol;
* root → nonroot: preservation of the incoming E_P symbol;
* nonroot → root: the canonical root-match relation;
* nonroot → nonroot: transport of the template edge and inclusion of
  complete reachable-root supports.

All statements hold for *any* choices of source R_P witnesses, so
no transversal or special enumeration is needed.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Root-to-root source edges are preserved by the exact auxiliary
embedding, since the edge symbol is fixed by the language action. -/
theorem source_root_root_edge
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (a b : RootsIn G k S)
    (hEdge : G.edge a.val b.val) :
    ReconstructedEdge G k B (.inl (ι a)) (.inl (ι b)) := by
  have hm :=
    (ι.map_rel_iff AuxiliaryRel.edge ![a,b]).2 hEdge
  have ht : (ι.toFun ∘ ![a,b]) = ![ι a,ι b] := by
    funext i
    fin_cases i <;> rfl
  rw [ht] at hm
  change B.rel AuxiliaryRel.edge ![ι a,ι b]
  simpa only [auxiliaryAction_on_edge] using hm

/-- If a source root a points to the centre of a realized source
nonroot pattern d, the corresponding E_P relation creates exactly
the expected reconstructed root-to-nonroot edge. -/
theorem source_root_nonroot_edge
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    {x : V}
    (d : SourceNonrootPattern G k S x)
    (a : RootsIn G k S)
    (hEdge : G.edge a.val x) :
    ReconstructedEdge G k B
      (.inl (ι a)) (.inr (d.toCanonical B ι)) := by
  let ys : Fin (d.n + 1) → RootsIn G k S :=
    Fin.cases a d.tuple
  have hInfo :=
    (auxiliaryRootStructure_root G k d.n S d.pattern d.tuple).mp
      d.realized
  have hE :
      (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.incoming d.pattern) ys := by
    apply (auxiliaryRootStructure_incoming G k d.n S d.pattern ys).2
    refine ⟨hInfo.1, ?_, ?_⟩
    · change G.edge (ys 0).val d.pattern.center
      simpa [ys, d.center_eq] using hEdge
    · intro i
      simpa [ys] using hInfo.2 i
  have hm :=
    (ι.map_rel_iff (AuxiliaryRel.incoming d.pattern) ys).2 hE
  have hB : B.rel
      (AuxiliaryRel.incoming
        (RootPattern.transportAut ι.lang d.pattern))
      (ι.toFun ∘ ys) := by
    change B.rel
      (AuxiliaryRel.incoming
        (RootPattern.transportAut ι.lang d.pattern))
      (ι.toFun ∘ ys) at hm
    exact hm
  change IncomingRealized G k B (ι a) (d.toCanonical B ι)
  refine ⟨d.n, RootPattern.transportAut ι.lang d.pattern,
    (ι.toFun ∘ ys), ?_, hB, ?_, ?_⟩
  · rfl
  · rfl
  · change Set.range (fun i : Fin d.n =>
        ι (ys (Fin.succ i))) =
      Set.range (ι.toFun ∘ d.tuple)
    congr 1

/-- A source nonroot-to-root edge lifts using the intrinsic
root-matching relation induced by its witnessed R_P enumeration. -/
theorem source_nonroot_root_edge
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    {x : V}
    (d : SourceNonrootPattern G k S x)
    (b : RootsIn G k S)
    (hEdge : G.edge x b.val) :
    ReconstructedEdge G k B
      (.inr (d.toCanonical B ι)) (.inl (ι b)) := by
  have hRoot : b.val ∈ G.roots k d.pattern.center := by
    refine ⟨b.property.2, ?_⟩
    rw [d.center_eq]
    exact G.reaches_of_edge hEdge
  rw [d.pattern.roots_eq] at hRoot
  obtain ⟨i, hi⟩ := hRoot
  have hInfo :=
    (auxiliaryRootStructure_root G k d.n S d.pattern d.tuple).mp
      d.realized
  have hSourcePoint : d.tuple i = b := by
    apply Subtype.ext
    exact (hInfo.2 i).trans hi
  have hB :
      B.rel (AuxiliaryRel.root
        (RootPattern.transportAut ι.lang d.pattern))
        (ι.toFun ∘ d.tuple) := by
    have hm :=
      (ι.map_rel_iff (AuxiliaryRel.root d.pattern) d.tuple).2
        d.realized
    change B.rel (AuxiliaryRel.root
      (RootPattern.transportAut ι.lang d.pattern))
      (ι.toFun ∘ d.tuple) at hm
    exact hm
  have hMatch : RootMatches G k B (d.toCanonical B ι)
      (ι.lang.1 b.val) (ι b) := by
    refine ⟨d.n, RootPattern.transportAut ι.lang d.pattern,
      (ι.toFun ∘ d.tuple), i, ?_, hB, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · change ι.lang.1 (d.pattern.tuple i) =
        ι.lang.1 b.val
      exact congrArg ι.lang.1 hi
    · change ι (d.tuple i) = ι b
      rw [hSourcePoint]
  change ∃ r : V, G.edge (d.toCanonical B ι).center r ∧
    RootMatches G k B (d.toCanonical B ι) r (ι b)
  refine ⟨ι.lang.1 b.val, ?_, hMatch⟩
  rw [d.toCanonical_center]
  exact (ι.lang.2 x b.val).2 hEdge

/-- An arbitrary pair of source R_P realizations lifts any template
nonroot-to-nonroot edge: complete root supports decrease along the
edge, so their images under the same root embedding also decrease. -/
theorem source_nonroot_nonroot_edge
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    {x y : V}
    (d : SourceNonrootPattern G k S x)
    (e : SourceNonrootPattern G k S y)
    (hEdge : G.edge x y) :
    ReconstructedEdge G k B
      (.inr (d.toCanonical B ι)) (.inr (e.toCanonical B ι)) := by
  change G.edge (d.toCanonical B ι).center
      (e.toCanonical B ι).center ∧
    (e.toCanonical B ι).support ⊆
      (d.toCanonical B ι).support
  constructor
  · rw [d.toCanonical_center, e.toCanonical_center]
    exact (ι.lang.2 x y).2 hEdge
  · rw [d.toCanonical_support_eq, e.toCanonical_support_eq]
    apply Set.image_mono
    intro r hr
    exact G.roots_antitone_edge k hEdge hr

end AllThoseEPPA.Applications.KOrientations
