import AllThoseEPPA.Applications.KOrientations.ReconstructionEdgeAction
import AllThoseEPPA.Applications.KOrientations.SecondStageRootDigraph

/-!
# The full reconstructed graph is genuinely oriented

We now discharge the nontrivial *mixed-sort* antisymmetry obligation.
If a realized E_P edge points from root a into a canonical non-root
(x,W), and an edge from (x,W) back to a were present, the canonical
root matching forces a to represent an actual template root r with
x→r. The E_P realization, moved into the original root structure
by faithful EPPA, gives r→x. This contradicts asymmetry of B₀.

The other two kinds of antiparallel edges are ruled out by the
faithful B₁ root graph and by template asymmetry, respectively.
We thereby obtain an actual Digraph on the complete tagged carrier.
The k-outdegree and exact d-root-closure axioms remain separate.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- A root-to-nonroot and its reverse edge cannot coexist.
This is the only cross-sort obstruction to an oriented reconstruction. -/
theorem reconstructedEdge_mixed_not_both
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (a : W) (p : CanonicalNonroot G k B)
    (hForward : ReconstructedEdge G k B (.inl a) (.inr p))
    (hBackward : ReconstructedEdge G k B (.inr p) (.inl a)) :
    False := by
  change IncomingRealized G k B a p at hForward
  change (∃ r : V, G.edge p.center r ∧
    RootMatches G k B p r a) at hBackward
  obtain ⟨n, P, ys, hc, hE, hy0, hU⟩ := hForward
  obtain ⟨r, hxr, hMatch⟩ := hBackward
  obtain ⟨m, Q, zs, j, _, hQ, hZ, hQj, hzj⟩ := hMatch
  have hTailRoot :
      B.rel (AuxiliaryRel.root P)
        (fun t : Fin n => ys (Fin.succ t)) :=
    faithful_auxiliary_incoming_implies_root
      G k S B ι hFaith P ys hE
  have haSupport : a ∈ p.support := by
    rw [← hZ]
    exact ⟨j, hzj⟩
  have haTail :
      a ∈ Set.range (fun t : Fin n => ys (Fin.succ t)) := by
    rw [hU]
    exact haSupport
  obtain ⟨i, hi⟩ := haTail
  have hEq : (fun t : Fin n => ys (Fin.succ t)) i = zs j := by
    calc
      ys (Fin.succ i) = a := hi
      _ = zs j := hzj.symm
  have hIndex : P.tuple i = r := by
    have hPQi :=
      (faithful_auxiliary_sameSupport_coordinateEq
        G k S B ι hFaith P Q
        (fun t : Fin n => ys (Fin.succ t)) zs
        hTailRoot hQ (hU.trans hZ.symm) i j).mpr hEq
    exact hPQi.trans hQj

  obtain ⟨f, ts, hPts, hSource⟩ :=
    faithful_auxiliary_relation_movable G k S B ι hFaith
      (AuxiliaryRel.incoming P) ys hE
  let g : G.graphAut := ι.lang⁻¹ * f.lang
  let Pg : RootPattern G k n := RootPattern.transportAut g P
  have hSource' :
      (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.incoming Pg) ts := by
    change (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.incoming
        (RootPattern.transportAut (ι.lang⁻¹ * f.lang) P)) ts at hSource
    exact hSource
  have hSrcData :=
    (auxiliaryRootStructure_incoming G k n S Pg ts).mp hSource'
  have hEdgeSrc : G.edge (ts 0).val Pg.center := hSrcData.2.1
  have hCoordSrc :
      (ts (Fin.succ i)).val = Pg.tuple i := hSrcData.2.2 i

  have hEqTs : ts 0 = ts (Fin.succ i) := by
    apply ι.injective
    calc
      ι (ts 0) = f (ys 0) := (hPts 0).symm
      _ = f (ys (Fin.succ i)) :=
        congrArg f (hy0.trans hi.symm)
      _ = ι (ts (Fin.succ i)) := hPts (Fin.succ i)
  have hFirst : (ts 0).val = g.1 r := by
    calc
      (ts 0).val = (ts (Fin.succ i)).val :=
        congrArg Subtype.val hEqTs
      _ = Pg.tuple i := hCoordSrc
      _ = g.1 (P.tuple i) := rfl
      _ = g.1 r := congrArg g.1 hIndex
  have hCenter : Pg.center = g.1 p.center := by
    change g.1 P.center = g.1 p.center
    exact congrArg g.1 hc
  have hBackG : G.edge (g.1 r) (g.1 p.center) := by
    rw [← hFirst, ← hCenter]
    exact hEdgeSrc
  have hForwardG : G.edge (g.1 p.center) (g.1 r) :=
    (g.2 p.center r).2 hxr
  exact (G.asymmetric hForwardG) hBackG

/-- The complete four-case reconstructed relation is asymmetric, and
therefore defines a genuine directed graph with no loops and no
antiparallel edges. -/
def faithfulReconstructedDigraph
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι) :
    Digraph (ReconstructedCarrier G k B) where
  edge := ReconstructedEdge G k B
  asymmetric := by
    intro x y hxy
    cases x with
    | inl a =>
        cases y with
        | inl b =>
            exact faithful_auxiliary_edge_asymm G k S B ι hFaith hxy
        | inr p =>
            intro hyx
            exact reconstructedEdge_mixed_not_both
              G k S B ι hFaith a p hxy hyx
    | inr p =>
        cases y with
        | inl a =>
            intro hyx
            exact reconstructedEdge_mixed_not_both
              G k S B ι hFaith a p hyx hxy
        | inr q =>
            exact reconstructedEdge_nonroot_asymm G k B p q hxy

@[simp] theorem faithfulReconstructedDigraph_edge
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (x y : ReconstructedCarrier G k B) :
    (faithfulReconstructedDigraph G k S B ι hFaith).edge x y ↔
      ReconstructedEdge G k B x y :=
  Iff.rfl

end AllThoseEPPA.Applications.KOrientations
