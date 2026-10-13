import AllThoseEPPA.Applications.KOrientations.SecondStageIncidence
import AllThoseEPPA.Automorphism

/-!
# Choice-independent matching between template roots and realized roots

This moves two root relations sharing the same realized support into
the original root structure simultaneously. Their coordinate matching
is forced by the template roots even with different centres.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- A realized root relation moved pointwise into the embedded source
induces the source relation with exact language relabelling. -/
private theorem root_source_of_moved
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    {n : ℕ} (P : RootPattern G k n)
    (xs : Fin n → W) (as : Fin n → RootsIn G k S)
    (ha : ∀ i, f (xs i) = ι (as i))
    (h : B.rel (AuxiliaryRel.root P) xs) :
    (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.root (RootPattern.transportAut (ι.lang⁻¹ * f.lang) P)) as := by
  have hlabel :
      (auxiliaryAction G k).onRel ι.lang
          (AuxiliaryRel.root (RootPattern.transportAut (ι.lang⁻¹ * f.lang) P)) =
      (auxiliaryAction G k).onRel f.lang (AuxiliaryRel.root P) := by
    change AuxiliaryRel.root
      (RootPattern.transportAut ι.lang
        (RootPattern.transportAut (ι.lang⁻¹ * f.lang) P)) =
      AuxiliaryRel.root (RootPattern.transportAut f.lang P)
    rw [← RootPattern.transportAut_mul]
    simp [← mul_assoc]
  have hmap : B.rel
        ((auxiliaryAction G k).onRel f.lang (AuxiliaryRel.root P))
        (f ∘ xs) :=
    (Structure.Automorphism.map_rel_iff f (AuxiliaryRel.root P) xs).2 h
  have htuple : (f ∘ xs) = (ι.toFun ∘ as) := by
    funext i
    exact ha i
  apply (ι.map_rel_iff
    (AuxiliaryRel.root (RootPattern.transportAut (ι.lang⁻¹ * f.lang) P)) as).1
  rw [hlabel, ← htuple]
  exact hmap

/-- If two realized root-label relations have the same unordered root
support, their template coordinates agree if and only if their
realized coordinates agree. The centres may be different. -/
theorem faithful_auxiliary_sameSupport_coordinateEq
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {n m : ℕ} (P : RootPattern G k n) (Q : RootPattern G k m)
    (xs : Fin n → W) (ys : Fin m → W)
    (hP : B.rel (AuxiliaryRel.root P) xs)
    (hQ : B.rel (AuxiliaryRel.root Q) ys)
    (hSupport : Set.range xs = Set.range ys)
    (i : Fin n) (j : Fin m) :
    P.tuple i = Q.tuple j ↔ xs i = ys j := by
  classical
  obtain ⟨f, hMove⟩ :=
    faithful_moves_relationClosure (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B ι hFaith
      (AuxiliaryRel.root P) xs hP
  have hX (t : Fin n) :
      ∃ a : RootsIn G k S, f (xs t) = ι a := by
    exact hMove (xs t)
      (B.subset_closureSet (Set.range xs) ⟨t, rfl⟩)
  have hY (t : Fin m) :
      ∃ a : RootsIn G k S, f (ys t) = ι a := by
    apply hMove (ys t)
    apply B.subset_closureSet (Set.range xs)
    rw [hSupport]
    exact ⟨t, rfl⟩
  let as : Fin n → RootsIn G k S := fun t => Classical.choose (hX t)
  let bs : Fin m → RootsIn G k S := fun t => Classical.choose (hY t)
  have ha : ∀ t : Fin n, f (xs t) = ι (as t) :=
    fun t => Classical.choose_spec (hX t)
  have hb : ∀ t : Fin m, f (ys t) = ι (bs t) :=
    fun t => Classical.choose_spec (hY t)
  let g : G.graphAut := ι.lang⁻¹ * f.lang
  have hSrcP :
      (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.root (RootPattern.transportAut g P)) as :=
    root_source_of_moved G k S B ι f P xs as ha hP
  have hSrcQ :
      (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.root (RootPattern.transportAut g Q)) bs :=
    root_source_of_moved G k S B ι f Q ys bs hb hQ
  have hCoordP : ∀ t, (as t).val = g.1 (P.tuple t) :=
    ((auxiliaryRootStructure_root G k n S
      (RootPattern.transportAut g P) as).mp hSrcP).2
  have hCoordQ : ∀ t, (bs t).val = g.1 (Q.tuple t) :=
    ((auxiliaryRootStructure_root G k m S
      (RootPattern.transportAut g Q) bs).mp hSrcQ).2
  constructor
  · intro heq
    apply f.toEquiv.injective
    calc
      f (xs i) = ι (as i) := ha i
      _ = ι (bs j) := by
        congr 1
        apply Subtype.ext
        calc
          (as i).val = g.1 (P.tuple i) := hCoordP i
          _ = g.1 (Q.tuple j) := congrArg g.1 heq
          _ = (bs j).val := (hCoordQ j).symm
      _ = f (ys j) := (hb j).symm
  · intro heq
    apply g.1.injective
    have hsub : as i = bs j := by
      apply ι.injective
      calc
        ι (as i) = f (xs i) := (ha i).symm
        _ = f (ys j) := congrArg f heq
        _ = ι (bs j) := hb j
    calc
      g.1 (P.tuple i) = (as i).val := (hCoordP i).symm
      _ = (bs j).val := congrArg Subtype.val hsub
      _ = g.1 (Q.tuple j) := hCoordQ j

end AllThoseEPPA.Applications.KOrientations
