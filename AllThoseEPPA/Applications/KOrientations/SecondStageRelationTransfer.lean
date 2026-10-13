import AllThoseEPPA.Applications.KOrientations.SecondWitness
import AllThoseEPPA.Applications.KOrientations.FaithfulLocalTransfer
import AllThoseEPPA.Automorphism

/-!
# Local transport and injectivity in the second-stage auxiliary witness

Faithfulness moves the closure of a realised relation tuple into the
root-only source.  As both the source embedding and the moving
automorphism carry a *language* component, the source label is
transported by `ι.lang⁻¹ * f.lang`, not merely by `f.lang`.

The resulting local transfer proves that every realised R_P tuple has
pairwise distinct coordinates, and every realised E_P tuple has
pairwise distinct **root coordinates** (the first coordinate of E_P
need not be distinct from the others).
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Move the entire realised auxiliary relation tuple into the source
root structure, keeping the **exact** relabelled relation.

The factor `ι.lang⁻¹` is essential: the EPPA embedding is not assumed
to have the identity language component. -/
theorem faithful_auxiliary_relation_movable
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {n : ℕ} (R : AuxiliaryRel G k n) (xs : Fin n → W)
    (hRel : B.rel R xs) :
    ∃ (f : Structure.Automorphism (auxiliaryAction G k) B)
      (ys : Fin n → RootsIn G k S),
      (∀ i, f (xs i) = ι (ys i)) ∧
      (auxiliaryRootStructure G k S).rel
        ((auxiliaryAction G k).onRel (ι.lang⁻¹ * f.lang) R) ys := by
  classical
  let act := auxiliaryAction G k
  obtain ⟨f, hmove⟩ :=
    faithful_moves_relationClosure act
      (auxiliaryRootStructure G k S) B ι hFaith R xs hRel
  have hExists (i : Fin n) :
      ∃ a : RootsIn G k S, f (xs i) = ι a := by
    exact hmove (xs i)
      (B.subset_closureSet (Set.range xs) ⟨i, rfl⟩)
  let ys : Fin n → RootsIn G k S :=
    fun i => Classical.choose (hExists i)
  have hPts : ∀ i : Fin n, f (xs i) = ι (ys i) :=
    fun i => Classical.choose_spec (hExists i)
  refine ⟨f, ys, hPts, ?_⟩
  have hTuple : (f ∘ xs) = (ι.toFun ∘ ys) := by
    funext i
    exact hPts i
  have hRelB :
      B.rel (act.onRel f.lang R) (f ∘ xs) :=
    (Structure.Automorphism.map_rel_iff f R xs).2 hRel
  have hAction :
      act.onRel ι.lang (act.onRel (ι.lang⁻¹ * f.lang) R) =
        act.onRel f.lang R := by
    change (auxiliaryAction G k).onRel ι.lang
      ((auxiliaryAction G k).onRel (ι.lang⁻¹ * f.lang) R) =
        (auxiliaryAction G k).onRel f.lang R
    rw [← Language.Action.onRel_mul]
    simp [← mul_assoc]
  apply (ι.map_rel_iff (act.onRel (ι.lang⁻¹ * f.lang) R) ys).1
  rw [hAction, ← hTuple]
  exact hRelB

/-- Every realised R_P tuple of the faithful second-stage witness is
injective. This is **not** assumed of arbitrary unrestricted EPPA
witnesses; it follows from relation-closure faithfulness. -/
theorem faithful_auxiliary_rootTuple_injective
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {n : ℕ} (P : RootPattern G k n) (xs : Fin n → W)
    (hRel : B.rel (AuxiliaryRel.root P) xs) :
    Function.Injective xs := by
  obtain ⟨f, ys, hPts, hSource⟩ :=
    faithful_auxiliary_relation_movable G k S B ι hFaith
      (AuxiliaryRel.root P) xs hRel
  let Q : RootPattern G k n :=
    RootPattern.transportAut (ι.lang⁻¹ * f.lang) P
  change (auxiliaryRootStructure G k S).rel
    (AuxiliaryRel.root Q) ys at hSource
  have hCoords : ∀ i, (ys i).val = Q.tuple i :=
    ((auxiliaryRootStructure_root G k n S Q ys).mp hSource).2
  have hInj : Function.Injective ys := by
    intro i j hij
    apply Q.injective
    calc
      Q.tuple i = (ys i).val := (hCoords i).symm
      _ = (ys j).val := congrArg Subtype.val hij
      _ = Q.tuple j := hCoords j
  intro i j hij
  apply hInj
  apply ι.injective
  calc
    ι (ys i) = f (xs i) := (hPts i).symm
    _ = f (xs j) := congrArg f hij
    _ = ι (ys j) := hPts j

/-- In a realised E_P tuple, the n pattern-root coordinates are
pairwise distinct. The leading vertex can coincide with a root, so
the statement deliberately excludes coordinate zero. -/
theorem faithful_auxiliary_incomingTail_injective
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {n : ℕ} (P : RootPattern G k n) (xs : Fin (n + 1) → W)
    (hRel : B.rel (AuxiliaryRel.incoming P) xs) :
    Function.Injective (fun i : Fin n => xs (Fin.succ i)) := by
  obtain ⟨f, ys, hPts, hSource⟩ :=
    faithful_auxiliary_relation_movable G k S B ι hFaith
      (AuxiliaryRel.incoming P) xs hRel
  let Q : RootPattern G k n :=
    RootPattern.transportAut (ι.lang⁻¹ * f.lang) P
  change (auxiliaryRootStructure G k S).rel
    (AuxiliaryRel.incoming Q) ys at hSource
  have hCoords : ∀ i, (ys (Fin.succ i)).val = Q.tuple i :=
    ((auxiliaryRootStructure_incoming G k n S Q ys).mp hSource).2.2
  have hInj : Function.Injective (fun i : Fin n => ys (Fin.succ i)) := by
    intro i j hij
    apply Q.injective
    calc
      Q.tuple i = (ys (Fin.succ i)).val := (hCoords i).symm
      _ = (ys (Fin.succ j)).val := congrArg Subtype.val hij
      _ = Q.tuple j := hCoords j
  intro i j hij
  apply hInj
  apply ι.injective
  calc
    ι (ys (Fin.succ i)) = f (xs (Fin.succ i)) :=
      (hPts (Fin.succ i)).symm
    _ = f (xs (Fin.succ j)) := congrArg f hij
    _ = ι (ys (Fin.succ j)) := hPts (Fin.succ j)

end AllThoseEPPA.Applications.KOrientations
