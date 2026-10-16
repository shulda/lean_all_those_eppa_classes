import AllThoseEPPA.Applications.KOrientations.SourceRootTupleClosed
import AllThoseEPPA.Applications.KOrientations.ReconstructionCarrier
import AllThoseEPPA.Applications.KOrientations.SecondStageSuccessorAxioms
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Realized R_P supports are unary-closed in the faithful B₁ witness

An R_P tuple in the root-only auxiliary source enumerates *all*
roots reachable from its template centre; hence its root set is
unary-closed (proved in SourceRootTupleClosed).

For a realized R_P tuple in B₁, faithfulness moves the tuple to
the source. Its function values are exactly the embedding-images
of source function values, while automorphisms preserve them exactly.
This transfers the closure condition back to the realized support.

The key consequence is that the support of every canonical non-root
p=(x,W) is an actual B₁ substructure, not just an arbitrary subset.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every realized auxiliary R_P tuple has unary-closed support
under the *full* second-stage set-valued function. -/
theorem faithful_auxiliary_rootTuple_isClosed
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {n : ℕ} (P : RootPattern G k n)
    (xs : Fin n → W)
    (hR : B.rel (AuxiliaryRel.root P) xs) :
    B.IsClosed (Set.range xs) := by
  obtain ⟨f, zs, hPts, hSource⟩ :=
    faithful_auxiliary_relation_movable G k S B ι hFaith
      (AuxiliaryRel.root P) xs hR
  have hSource' :
      (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.root
          (RootPattern.transportAut (ι.lang⁻¹ * f.lang) P)) zs := by
    change (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.root
        (RootPattern.transportAut (ι.lang⁻¹ * f.lang) P)) zs at hSource
    exact hSource
  have hSourceClosed :
      (auxiliaryRootStructure G k S).IsClosed (Set.range zs) :=
    auxiliarySource_rootTuple_isClosed G k S
      (RootPattern.transportAut (ι.lang⁻¹ * f.lang) P)
      zs hSource'

  intro ar F vs hvs z hz
  cases F with
  | successor =>
      obtain ⟨i, hi⟩ := hvs 0
      have htup : vs = ![vs 0] := by
        funext t
        fin_cases t
        rfl
      rw [htup] at hz
      have hzin : z ∈ B.func AuxiliaryFunc.successor ![xs i] := by
        simpa only [← hi] using hz
      have hFz : f z ∈ B.func
          AuxiliaryFunc.successor ![f (xs i)] :=
        (auxiliary_automorphism_successor_iff G k B
          f (xs i) z).mp hzin
      have hZimage : f z ∈ B.func
          AuxiliaryFunc.successor ![ι (zs i)] := by
        rw [← hPts i]
        exact hFz
      have hMap := ι.map_func AuxiliaryFunc.successor ![zs i]
      have htupS :
          (ι.toFun ∘ ![zs i]) = ![ι (zs i)] := by
        funext t
        fin_cases t
        rfl
      rw [htupS] at hMap
      have hSetEq :
          Structure.imageSet ι.toFun
              ((auxiliaryRootStructure G k S).func
                AuxiliaryFunc.successor ![zs i]) =
            B.func AuxiliaryFunc.successor ![ι (zs i)] := by
        simpa only [auxiliaryAction_on_successor] using hMap
      rw [← hSetEq] at hZimage
      obtain ⟨b, hbSource, hfb⟩ := hZimage
      have hbRange : b ∈ Set.range zs := by
        apply hSourceClosed AuxiliaryFunc.successor ![zs i]
        · intro t
          fin_cases t
          exact ⟨i, rfl⟩
        · exact hbSource
      obtain ⟨j, hj⟩ := hbRange
      have hEqf : f z = f (xs j) := by
        calc
          f z = ι b := hfb.symm
          _ = ι (zs j) := congrArg ι hj.symm
          _ = f (xs j) := (hPts j).symm
      exact ⟨j, (f.toEquiv.injective hEqf).symm⟩

/-- A realized R_P tuple generates exactly its unordered support
as a closed B₁ substructure. -/
theorem faithful_auxiliary_rootTuple_closure_eq
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {n : ℕ} (P : RootPattern G k n)
    (xs : Fin n → W)
    (hR : B.rel (AuxiliaryRel.root P) xs) :
    B.closureSet (Set.range xs) = Set.range xs :=
  B.closureSet_eq_self
    (faithful_auxiliary_rootTuple_isClosed G k S B ι hFaith P xs hR)

/-- The intrinsic support of any canonical non-root p=(x,W)
is unary-closed in B₁, independently of its chosen realization. -/
theorem canonicalNonroot_support_isClosed
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p : CanonicalNonroot G k B) :
    B.IsClosed p.support := by
  obtain ⟨n, P, xs, _, hR, hU⟩ := p.witnessed
  rw [← hU]
  exact faithful_auxiliary_rootTuple_isClosed G k S B ι hFaith P xs hR

end AllThoseEPPA.Applications.KOrientations
