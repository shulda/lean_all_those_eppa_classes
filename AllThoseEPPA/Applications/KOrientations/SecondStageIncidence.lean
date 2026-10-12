import AllThoseEPPA.Applications.KOrientations.SecondStageRelationTransfer

/-!
# Relation incidence in the second-stage witness

A realized incoming-edge symbol E_P includes a rooted realization of
the same label P in its trailing coordinates. This is obvious in the
original auxiliary root structure, but it is NOT built into arbitrary
structures produced by unrestricted EPPA.

The implication is recovered from irreducible-structure faithfulness,
using the exact label correction for the possibly nontrivial source
embedding.  The converse is intentionally not asserted.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- In the literal source root structure, the trailing root tuple
of E_P automatically realizes R_P. -/
theorem auxiliarySource_incoming_implies_root
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    {n : ℕ} (P : RootPattern G k n)
    (xs : Fin (n + 1) → RootsIn G k S)
    (hRel : (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.incoming P) xs) :
    (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.root P)
      (fun i : Fin n => xs (Fin.succ i)) := by
  change P.center ∈ S ∧ G.edge (xs 0).val P.center ∧
    (∀ i, (xs (Fin.succ i)).val = P.tuple i) at hRel
  exact ⟨hRel.1, hRel.2.2⟩

/-- The same incidence axiom holds in any irreducible-structure
faithful second-stage EPPA witness. In particular, an E_P-tuple
cannot create a 'dangling' root label absent from R_P. -/
theorem faithful_auxiliary_incoming_implies_root
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {n : ℕ} (P : RootPattern G k n)
    (xs : Fin (n + 1) → W)
    (hRel : B.rel (AuxiliaryRel.incoming P) xs) :
    B.rel (AuxiliaryRel.root P)
      (fun i : Fin n => xs (Fin.succ i)) := by
  obtain ⟨f, ys, hPts, hSource⟩ :=
    faithful_auxiliary_relation_movable G k S B ι hFaith
      (AuxiliaryRel.incoming P) xs hRel
  let Q : RootPattern G k n :=
    RootPattern.transportAut (ι.lang⁻¹ * f.lang) P
  change (auxiliaryRootStructure G k S).rel
    (AuxiliaryRel.incoming Q) ys at hSource
  have hRootSource :
      (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.root Q)
        (fun i : Fin n => ys (Fin.succ i)) :=
    auxiliarySource_incoming_implies_root G k S Q ys hSource
  have hRootB :
      B.rel ((auxiliaryAction G k).onRel ι.lang
        (AuxiliaryRel.root Q))
        (ι.toFun ∘ (fun i : Fin n => ys (Fin.succ i))) :=
    (ι.map_rel_iff (AuxiliaryRel.root Q)
      (fun i : Fin n => ys (Fin.succ i))).2 hRootSource
  have hLabel :
      (auxiliaryAction G k).onRel ι.lang
        (AuxiliaryRel.root Q) =
      (auxiliaryAction G k).onRel f.lang
        (AuxiliaryRel.root P) := by
    change AuxiliaryRel.root (RootPattern.transportAut ι.lang Q) =
      AuxiliaryRel.root (RootPattern.transportAut f.lang P)
    change AuxiliaryRel.root
        (RootPattern.transportAut ι.lang
          (RootPattern.transportAut (ι.lang⁻¹ * f.lang) P)) =
      AuxiliaryRel.root (RootPattern.transportAut f.lang P)
    rw [← RootPattern.transportAut_mul]
    simp [← mul_assoc]
  have hTuple :
      (ι.toFun ∘ (fun i : Fin n => ys (Fin.succ i))) =
      (f ∘ (fun i : Fin n => xs (Fin.succ i))) := by
    funext i
    exact (hPts (Fin.succ i)).symm
  have hAfter :
      B.rel ((auxiliaryAction G k).onRel f.lang
        (AuxiliaryRel.root P))
        (f ∘ (fun i : Fin n => xs (Fin.succ i))) := by
    rw [← hLabel, ← hTuple]
    exact hRootB
  exact (Structure.Automorphism.map_rel_iff f
    (AuxiliaryRel.root P)
    (fun i : Fin n => xs (Fin.succ i))).1 hAfter

end AllThoseEPPA.Applications.KOrientations
