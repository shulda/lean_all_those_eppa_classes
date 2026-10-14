import AllThoseEPPA.Applications.KOrientations.ReconstructionEdges
import AllThoseEPPA.Applications.KOrientations.CommonMoveRootRigidity
import AllThoseEPPA.Automorphism

/-!
# Local root-to-nonroot edge equivalence

Fix one automorphism f of the auxiliary B₁ witness. Suppose f sends
the root a to an embedded original source root t, and also sends all
of a reconstructed nonroot's canonical support W into that source.

Then the intrinsic existential E_P edge test is equivalent to the
single template edge t → (ι.lang⁻¹*f.lang)(x). The reverse direction
constructs an actual E_P tuple from any R_P realization of (x,W).
This is the root/nonroot case of the paper's local Claim P2, with
full preservation *and reflection*, without quotient representatives.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- An incoming E_P relation can be tested in the source after
any fixed automorphism f sending **every coordinate** into that
source. The relabelled symbol must use ι.lang⁻¹*f.lang. -/
private theorem auxiliary_incoming_iff_moved_source
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    {n : ℕ} (P : RootPattern G k n)
    (ys : Fin (n+1) → W)
    (ts : Fin (n+1) → RootsIn G k S)
    (hPts : ∀ i, f (ys i) = ι (ts i)) :
    B.rel (AuxiliaryRel.incoming P) ys ↔
      (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.incoming
          (RootPattern.transportAut (ι.lang⁻¹*f.lang) P)) ts := by
  let g : G.graphAut := ι.lang⁻¹*f.lang
  have hLabel :
      (auxiliaryAction G k).onRel ι.lang
        (AuxiliaryRel.incoming (RootPattern.transportAut g P)) =
      (auxiliaryAction G k).onRel f.lang
        (AuxiliaryRel.incoming P) := by
    change AuxiliaryRel.incoming
      (RootPattern.transportAut ι.lang
        (RootPattern.transportAut (ι.lang⁻¹*f.lang) P)) =
      AuxiliaryRel.incoming (RootPattern.transportAut f.lang P)
    rw [← RootPattern.transportAut_mul]
    simp [← mul_assoc]
  have hTuple : (f ∘ ys) = (ι.toFun ∘ ts) := by
    funext i
    exact hPts i
  have hF := Structure.Automorphism.map_rel_iff
    f (AuxiliaryRel.incoming P) ys
  have hSource := ι.map_rel_iff
    (AuxiliaryRel.incoming (RootPattern.transportAut g P)) ts
  calc
    B.rel (AuxiliaryRel.incoming P) ys ↔
        B.rel ((auxiliaryAction G k).onRel f.lang
          (AuxiliaryRel.incoming P)) (f ∘ ys) := hF.symm
    _ ↔ B.rel ((auxiliaryAction G k).onRel ι.lang
          (AuxiliaryRel.incoming (RootPattern.transportAut g P)))
          (ι.toFun ∘ ts) := by rw [hLabel, ← hTuple]
    _ ↔ (auxiliaryRootStructure G k S).rel
          (AuxiliaryRel.incoming (RootPattern.transportAut g P)) ts :=
      hSource

/-- The analogous source-transport proof for a realized root tuple
under the same fixed f (not a newly chosen faithful mover). -/
private theorem auxiliary_root_relation_of_common_move
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    {n : ℕ} (P : RootPattern G k n)
    (xs : Fin n → W) (ts : Fin n → RootsIn G k S)
    (hPts : ∀ i, f (xs i) = ι (ts i))
    (hRel : B.rel (AuxiliaryRel.root P) xs) :
    (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.root
        (RootPattern.transportAut (ι.lang⁻¹*f.lang) P)) ts := by
  let g : G.graphAut := ι.lang⁻¹*f.lang
  have hLabel :
      (auxiliaryAction G k).onRel ι.lang
        (AuxiliaryRel.root (RootPattern.transportAut g P)) =
      (auxiliaryAction G k).onRel f.lang
        (AuxiliaryRel.root P) := by
    change AuxiliaryRel.root
      (RootPattern.transportAut ι.lang
        (RootPattern.transportAut (ι.lang⁻¹*f.lang) P)) =
      AuxiliaryRel.root (RootPattern.transportAut f.lang P)
    rw [← RootPattern.transportAut_mul]
    simp [← mul_assoc]
  have hF : B.rel
      ((auxiliaryAction G k).onRel f.lang (AuxiliaryRel.root P))
      (f ∘ xs) :=
    (Structure.Automorphism.map_rel_iff
      f (AuxiliaryRel.root P) xs).2 hRel
  have hTuple : (f ∘ xs) = (ι.toFun ∘ ts) := by
    funext i
    exact hPts i
  apply (ι.map_rel_iff
    (AuxiliaryRel.root (RootPattern.transportAut g P)) ts).1
  rw [hLabel, ← hTuple]
  exact hF

/-- The reconstructed mixed edge a→(x,W) is **equivalent** to the
template edge from the source image of a to the transformed x. -/
theorem local_root_nonroot_edge_iff
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (a : W) (t : RootsIn G k S)
    (hA : f a = ι t)
    (p : CanonicalNonroot G k B)
    (hP : ∀ w ∈ p.support,
      ∃ s : RootsIn G k S, f w = ι s) :
    ReconstructedEdge G k B (.inl a) (.inr p) ↔
      G.edge t.val ((ι.lang⁻¹*f.lang : G.graphAut).1 p.center) := by
  classical
  let g : G.graphAut := ι.lang⁻¹*f.lang
  constructor
  · intro hIncoming
    obtain ⟨n,P,ys,hCentre,hRel,hZero,hU⟩ := hIncoming
    have hPart (i : Fin n) :
        ∃ s : RootsIn G k S, f (ys (Fin.succ i)) = ι s := by
      apply hP
      rw [← hU]
      exact ⟨i,rfl⟩
    let ts : Fin (n+1) → RootsIn G k S :=
      Fin.cases t (fun i => Classical.choose (hPart i))
    have hPts : ∀ i, f (ys i) = ι (ts i) := by
      intro i
      refine Fin.cases ?_ ?_ i
      · change f (ys 0) = ι t
        simpa only [hZero] using hA
      · intro j
        change f (ys (Fin.succ j)) =
          ι (Classical.choose (hPart j))
        exact Classical.choose_spec (hPart j)
    have hSource :=
      (auxiliary_incoming_iff_moved_source
        G k S B ι f P ys ts hPts).mp hRel
    have hData :=
      (auxiliaryRootStructure_incoming G k n S
        (RootPattern.transportAut g P) ts).mp hSource
    have hEdge : G.edge t.val (g.1 P.center) := by
      simpa [ts, RootPattern.transportAut] using hData.2.1
    simpa only [hCentre] using hEdge
  · intro hEdge
    obtain ⟨n,P,xs,hCentre,hRel,hU⟩ := p.witnessed
    have hPart (i : Fin n) :
        ∃ s : RootsIn G k S, f (xs i) = ι s := by
      apply hP
      rw [← hU]
      exact ⟨i,rfl⟩
    let rs : Fin n → RootsIn G k S :=
      fun i => Classical.choose (hPart i)
    have hrs : ∀ i, f (xs i) = ι (rs i) :=
      fun i => Classical.choose_spec (hPart i)
    have hSourceR :=
      auxiliary_root_relation_of_common_move
        G k S B ι f P xs rs hrs hRel
    have hRData :=
      (auxiliaryRootStructure_root G k n S
        (RootPattern.transportAut g P) rs).mp hSourceR
    let ys : Fin (n+1) → W := Fin.cases a xs
    let ts : Fin (n+1) → RootsIn G k S :=
      Fin.cases t rs
    have hPts : ∀ i, f (ys i) = ι (ts i) := by
      intro i
      refine Fin.cases ?_ ?_ i
      · change f a = ι t
        exact hA
      · intro j
        change f (xs j) = ι (rs j)
        exact hrs j
    have hSourceE :
        (auxiliaryRootStructure G k S).rel
          (AuxiliaryRel.incoming
            (RootPattern.transportAut g P)) ts := by
      apply (auxiliaryRootStructure_incoming G k n S
        (RootPattern.transportAut g P) ts).2
      refine ⟨hRData.1, ?_, ?_⟩
      · change G.edge t.val (g.1 P.center)
        simpa only [hCentre] using hEdge
      · intro i
        simpa [ts, RootPattern.transportAut] using hRData.2 i
    have hIncoming : B.rel (AuxiliaryRel.incoming P) ys :=
      (auxiliary_incoming_iff_moved_source
        G k S B ι f P ys ts hPts).mpr hSourceE
    change IncomingRealized G k B a p
    refine ⟨n,P,ys,hCentre,hIncoming,?_,?_⟩
    · rfl
    · change Set.range xs = p.support
      exact hU

end AllThoseEPPA.Applications.KOrientations
