import AllThoseEPPA.Applications.KOrientations.SourcePatternRealization
import AllThoseEPPA.Applications.KOrientations.SecondStageRelationTransfer
import AllThoseEPPA.Automorphism

/-!
# Lift template nonroot neighbours to realized auxiliary root patterns

Fix a realized R_P tuple in an irreducible-structure faithful second
witness B₁. If the distinguished source S is successor-closed, an
outgoing template edge from P.center to the centre of another
root-pattern Q forces a realized R_Q tuple with support INCLUDED
in that of the original R_P tuple.

The construction moves the whole original relation tuple into the
source once, realizes the translated Q in that source, then transports
the new tuple back along the same B₁ automorphism. This is the
existence/surjectivity half of the nonroot-to-nonroot neighbour map.
It does not assume that all vertices of the ambient template B₀
have reachable roots: the target Q is assumed to be an admissible
root-pattern (hence has nonempty reachable root set).
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- A template outgoing edge x→y between two nonroot labels with
nonempty root sets lifts to a B₁-realized R_Q tuple whose support
lies inside any realized R_P support for x. -/
theorem faithful_auxiliary_lift_nested_rootPattern
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {n m : ℕ}
    (P : RootPattern G k n) (Q : RootPattern G k m)
    (hEdge : G.edge P.center Q.center)
    (xs : Fin n → W) (hR : B.rel (AuxiliaryRel.root P) xs) :
    ∃ ys : Fin m → W,
      B.rel (AuxiliaryRel.root Q) ys ∧
      Set.range ys ⊆ Set.range xs := by
  classical
  obtain ⟨f, ts, hPts, hRelP⟩ :=
    faithful_auxiliary_relation_movable G k S B ι hFaith
      (AuxiliaryRel.root P) xs hR
  let g : G.graphAut := ι.lang⁻¹ * f.lang
  let Pg : RootPattern G k n := RootPattern.transportAut g P
  let Qg : RootPattern G k m := RootPattern.transportAut g Q
  have hSrcP :
      (auxiliaryRootStructure G k S).rel (AuxiliaryRel.root Pg) ts :=
    hRelP
  have hCenterP : g.1 P.center ∈ S := by
    exact ((auxiliaryRootStructure_root G k n S Pg ts).mp hSrcP).1
  have hMovedEdge : G.edge (g.1 P.center) (g.1 Q.center) :=
    (g.2 P.center Q.center).2 hEdge
  have hCenterQ : Qg.center ∈ S := by
    change g.1 Q.center ∈ S
    exact hClosed (g.1 P.center) (g.1 Q.center)
      hCenterP (G.reaches_of_edge hMovedEdge)
  obtain ⟨us, hSrcQ⟩ :=
    auxiliarySource_realizes_rootPattern
      G k S hClosed Qg hCenterQ
  let ys : Fin m → W := fun j => f.symm (ι (us j))
  have hLabel :
      (auxiliaryAction G k).onRel ι.lang (AuxiliaryRel.root Qg) =
      (auxiliaryAction G k).onRel f.lang (AuxiliaryRel.root Q) := by
    change AuxiliaryRel.root
      (RootPattern.transportAut ι.lang
        (RootPattern.transportAut (ι.lang⁻¹ * f.lang) Q)) =
      AuxiliaryRel.root (RootPattern.transportAut f.lang Q)
    rw [← RootPattern.transportAut_mul]
    simp [← mul_assoc]
  have hEmbed :
      B.rel ((auxiliaryAction G k).onRel ι.lang
        (AuxiliaryRel.root Qg)) (ι.toFun ∘ us) :=
    (ι.map_rel_iff (AuxiliaryRel.root Qg) us).2 hSrcQ
  have hTuple : (f ∘ ys) = (ι.toFun ∘ us) := by
    funext j
    exact Structure.Automorphism.apply_symm_apply f (ι (us j))
  have hRelMapped :
      B.rel ((auxiliaryAction G k).onRel f.lang
        (AuxiliaryRel.root Q)) (f ∘ ys) := by
    rw [← hLabel, hTuple]
    exact hEmbed
  have hRel :
      B.rel (AuxiliaryRel.root Q) ys :=
    (Structure.Automorphism.map_rel_iff f
      (AuxiliaryRel.root Q) ys).1 hRelMapped
  have hCoordP (i : Fin n) :
      (ts i).val = g.1 (P.tuple i) :=
    ((auxiliaryRootStructure_root G k n S Pg ts).mp hSrcP).2 i
  have hCoordQ (j : Fin m) :
      (us j).val = g.1 (Q.tuple j) :=
    ((auxiliaryRootStructure_root G k m S Qg us).mp hSrcQ).2 j
  refine ⟨ys, hRel, ?_⟩
  intro w hw
  obtain ⟨j, rfl⟩ := hw
  have hRootQ : Q.tuple j ∈ G.roots k Q.center := by
    rw [Q.roots_eq]
    exact ⟨j, rfl⟩
  have hRootP : Q.tuple j ∈ G.roots k P.center :=
    G.roots_antitone_edge k hEdge hRootQ
  rw [P.roots_eq] at hRootP
  obtain ⟨i, hi⟩ := hRootP
  have hTsUs : ts i = us j := by
    apply Subtype.ext
    calc
      (ts i).val = g.1 (P.tuple i) := hCoordP i
      _ = g.1 (Q.tuple j) := congrArg g.1 hi
      _ = (us j).val := (hCoordQ j).symm
  refine ⟨i, ?_⟩
  calc
    xs i = f.symm (f (xs i)) :=
      (Structure.Automorphism.symm_apply_apply f (xs i)).symm
    _ = f.symm (ι (ts i)) := congrArg f.symm (hPts i)
    _ = f.symm (ι (us j)) :=
      congrArg (fun t : RootsIn G k S => f.symm (ι t)) hTsUs
    _ = ys j := rfl

end AllThoseEPPA.Applications.KOrientations
