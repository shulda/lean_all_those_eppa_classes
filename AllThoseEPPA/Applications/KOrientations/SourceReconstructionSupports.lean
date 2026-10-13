import AllThoseEPPA.Applications.KOrientations.SourceReconstructionPaths
import AllThoseEPPA.Applications.KOrientations.SecondStageExactUnaryClosure

/-!
# Exact support of the lifted source copy

The source-copy map respects supports in the strongest possible sense:
for each vertex x∈S, its reconstructed support is exactly the image
under the auxiliary embedding ι₁ of the ambient B₀-root set of x,
viewed inside the distinguished source root sort.

The nonroot case uses the full R_P enumeration. The root case uses
the checked exact singleton unary closure in B₁ and the exact
set-valued function preservation of ι₁.

This is the bridge from source path lifting to reachability of every
root in every source-copy support, with no choice of representatives.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The support of an embedded source root agrees exactly with the
embedded set of all its ambient reachable roots. -/
theorem source_root_support_eq
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (a : RootsIn G k S) :
    B.closureAtSet (ι a) =
      ι.toFun '' {r : RootsIn G k S | r.val ∈ G.roots k a.val} := by
  have hm := ι.map_func AuxiliaryFunc.successor ![a]
  have htup : (ι.toFun ∘ ![a]) = ![ι a] := by
    funext i
    fin_cases i
    rfl
  rw [htup] at hm
  have hEmbedding :
      ι.toFun '' ((auxiliaryRootStructure G k S).func
          AuxiliaryFunc.successor ![a]) =
        B.func AuxiliaryFunc.successor ![ι a] := by
    simpa only [auxiliaryAction_on_successor] using hm
  have hSource :
      (auxiliaryRootStructure G k S).func
        AuxiliaryFunc.successor ![a] =
        {r : RootsIn G k S | r.val ∈ G.roots k a.val} := by
    ext r
    change G.Reaches a.val r.val ↔
      (G.IsRoot k r.val ∧ G.Reaches a.val r.val)
    exact ⟨fun h => ⟨r.property.2, h⟩, fun h => h.2⟩
  calc
    B.closureAtSet (ι a) =
        B.func AuxiliaryFunc.successor ![ι a] :=
      faithful_auxiliary_closureAt_eq_successors
        G k S B ι hFaith (ι a)
    _ = ι.toFun '' ((auxiliaryRootStructure G k S).func
          AuxiliaryFunc.successor ![a]) := hEmbedding.symm
    _ = ι.toFun '' {r : RootsIn G k S |
          r.val ∈ G.roots k a.val} :=
      congrArg (fun T : Set (RootsIn G k S) => ι.toFun '' T) hSource

/-- Every source vertex, root or nonroot, has support equal to the
image of its complete ambient B₀ root set. -/
theorem sourceReconstructedVertex_support_eq
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (x : {a : V // a ∈ S}) :
    reconstructedSupport G k B
      (sourceReconstructedVertex G k S hClosed hRooted B ι x) =
      ι.toFun '' {r : RootsIn G k S |
        r.val ∈ G.roots k x.val} := by
  classical
  by_cases hr : G.IsRoot k x.val
  · simp only [sourceReconstructedVertex, dif_pos hr]
    change B.closureAtSet (ι (⟨x.val,x.property,hr⟩ : RootsIn G k S)) =
      ι.toFun '' {r : RootsIn G k S | r.val ∈ G.roots k x.val}
    exact source_root_support_eq G k S B ι hFaith
      ⟨x.val,x.property,hr⟩
  · simp only [sourceReconstructedVertex, dif_neg hr]
    change ((chosenSourceNonroot G k S hClosed hRooted
      x.val x.property hr).toCanonical B ι).support =
        ι.toFun '' {r : RootsIn G k S | r.val ∈ G.roots k x.val}
    exact (chosenSourceNonroot G k S hClosed hRooted
      x.val x.property hr).toCanonical_support_eq B ι

/-- All roots of source vertices are actual reached root vertices
of the reconstructed graph under the canonical source-copy map. -/
theorem sourceReconstructedVertex_support_reachable
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (x : {a : V // a ∈ S}) (r : W)
    (hr : r ∈ reconstructedSupport G k B
      (sourceReconstructedVertex G k S hClosed hRooted B ι x)) :
    (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
      (sourceReconstructedVertex G k S hClosed hRooted B ι x)
      (.inl r) := by
  rw [sourceReconstructedVertex_support_eq
      G k S hClosed hRooted B ι hFaith x] at hr
  obtain ⟨a, ha, hra⟩ := hr
  have hReach := sourceReconstructedVertex_preserves_reaches
      G k S hClosed hRooted B ι hFaith x.property ha.2
  have hTarget :
      sourceReconstructedVertex G k S hClosed hRooted B ι
        ⟨a.val, hClosed x.val a.val x.property ha.2⟩ =
      (.inl (ι a) : ReconstructedCarrier G k B) := by
    have hRoot : G.IsRoot k a.val := a.property.2
    simp only [sourceReconstructedVertex, dif_pos hRoot]
    rfl
  rw [hTarget] at hReach
  have hEq : ι a = r := hra
  simpa only [hEq] using hReach

end AllThoseEPPA.Applications.KOrientations
