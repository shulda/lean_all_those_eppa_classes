import AllThoseEPPA.Applications.KOrientations.ReconstructedDigraph
import AllThoseEPPA.Applications.KOrientations.SecondStageRootTupleClosed
import AllThoseEPPA.Applications.KOrientations.SecondStageSuccessorAxioms
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Reconstructed supports decrease along every oriented edge

The canonical support of a B₁-root vertex is its one-point unary
closure, while the support of a canonical non-root (x,W) is W.

The delicate case is a root-to-nonroot edge witnessed by E_P. Move
the entire incoming relation tuple into the original root structure:
its first vertex points to the template centre and thus reaches each
enumerated root. Exact embedding and B₁ automorphism transport put
every element of W in the source root's unary successor closure.

All four edge cases then give support(target) ⊆ support(source).
Consequently the same holds along every directed path. This does not
yet assert equality of supports with the final graph's root sets.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- If an E_P tuple witnesses an edge from a B₁-root a to a
reconstructed non-root p=(x,W), every element of W is contained in
the unary successor set of a in B₁. -/
theorem faithful_incoming_support_subset_successors
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (a : W) (p : CanonicalNonroot G k B)
    (h : IncomingRealized G k B a p) :
    p.support ⊆ B.func AuxiliaryFunc.successor ![a] := by
  obtain ⟨n, P, ys, hc, hE, ha, hU⟩ := h
  obtain ⟨f, ts, hPts, hSource⟩ :=
    faithful_auxiliary_relation_movable G k S B ι hFaith
      (AuxiliaryRel.incoming P) ys hE
  let g : G.graphAut := ι.lang⁻¹ * f.lang
  let Pg : RootPattern G k n := RootPattern.transportAut g P
  have hSrc :
      (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.incoming Pg) ts := by
    change (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.incoming
        (RootPattern.transportAut (ι.lang⁻¹ * f.lang) P)) ts at hSource
    exact hSource
  have hSrcData :=
    (auxiliaryRootStructure_incoming G k n S Pg ts).mp hSrc
  have hEdgeSrc : G.edge (ts 0).val Pg.center := hSrcData.2.1
  have hCoords : ∀ i, (ts (Fin.succ i)).val = Pg.tuple i :=
    hSrcData.2.2
  intro w hw
  have hTail : w ∈ Set.range (fun i : Fin n => ys (Fin.succ i)) := by
    rw [hU]
    exact hw
  obtain ⟨i, hi⟩ := hTail
  have hRoot : (ts (Fin.succ i)).val ∈ G.roots k Pg.center := by
    rw [Pg.roots_eq]
    exact ⟨i, (hCoords i).symm⟩
  have hReach : G.Reaches (ts 0).val (ts (Fin.succ i)).val :=
    G.reaches_trans (G.reaches_of_edge hEdgeSrc) hRoot.2
  have hEmb :
      ι (ts (Fin.succ i)) ∈
        B.func AuxiliaryFunc.successor ![ι (ts 0)] :=
    (auxiliary_embedding_successor_iff G k S B ι
      (ts 0) (ts (Fin.succ i))).mp hReach
  have hfa : f a = ι (ts 0) := by
    calc
      f a = f (ys 0) := congrArg f ha.symm
      _ = ι (ts 0) := hPts 0
  have hfw : f w = ι (ts (Fin.succ i)) := by
    calc
      f w = f (ys (Fin.succ i)) := congrArg f hi.symm
      _ = ι (ts (Fin.succ i)) := hPts (Fin.succ i)
  have hImage :
      f w ∈ B.func AuxiliaryFunc.successor ![f a] := by
    rw [hfw, hfa]
    exact hEmb
  exact (auxiliary_automorphism_successor_iff G k B f a w).mpr hImage

/-- Root-to-nonroot edges make supports decrease, including every
root in the potentially higher-arity realized E_P relation. -/
theorem faithful_incoming_support_subset_closure
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (a : W) (p : CanonicalNonroot G k B)
    (h : IncomingRealized G k B a p) :
    p.support ⊆ B.closureAtSet a := by
  exact (faithful_incoming_support_subset_successors
    G k S B ι hFaith a p h).trans
    (auxiliary_successorValue_subset_closureAt G k B a)

/-- The actual four-case reconstructed edge relation is
antitone on intrinsic supports. -/
theorem faithful_reconstructedEdge_support_antitone
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {x y : ReconstructedCarrier G k B}
    (h : ReconstructedEdge G k B x y) :
    reconstructedSupport G k B y ⊆
      reconstructedSupport G k B x := by
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          exact faithful_auxiliary_edge_closure_monotone
            G k S B ι hFaith h
      | inr p =>
          exact faithful_incoming_support_subset_closure
            G k S B ι hFaith a p h
  | inr p =>
      cases y with
      | inl a =>
          have ha : a ∈ p.support :=
            reconstructedEdge_nonroot_root_mem_support G k B p a h
          apply B.closureSet_minimal
            (canonicalNonroot_support_isClosed G k S B ι hFaith p)
          intro z hz
          have hza : z = a := by simpa using hz
          subst z
          exact ha
      | inr q =>
          exact reconstructedEdge_nonroot_nonroot_support G k B p q h

/-- Support inclusion extends from edges to *all finite oriented
paths* in the faithful reconstructed graph. -/
theorem faithful_reconstructed_reaches_support_antitone
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {x y : ReconstructedCarrier G k B}
    (h : (faithfulReconstructedDigraph G k S B ι hFaith).Reaches x y) :
    reconstructedSupport G k B y ⊆
      reconstructedSupport G k B x := by
  induction h with
  | refl _ =>
      exact Set.Subset.rfl
  | step he _ ih =>
      exact ih.trans
        (faithful_reconstructedEdge_support_antitone
          G k S B ι hFaith he)

end AllThoseEPPA.Applications.KOrientations
