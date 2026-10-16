import AllThoseEPPA.Applications.KOrientations.ReconstructionVertexAction
import AllThoseEPPA.Applications.KOrientations.SecondStageExactUnaryClosure
import AllThoseEPPA.Automorphism
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Reconstructed canonical supports are automorphism-equivariant

The vertex permutation induced by a B₁ automorphism f must transport
not only the edge relation, but also each intrinsic root support.
For nonroots (x,W), this is definitional: W maps to f''W.
For roots a∈B₁, the support is the one-point unary closure. We use
faithful exact unary closure and the exact map_func equality to
show closure(f a)=f''closure(a), even though the general unrestricted
EPPA witness did not initially have this property by construction.

This is a key input for the eventual coherent group-action gluing
and the support-based local isomorphism.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- A B₁ automorphism sends singleton unary closures to singleton
unary closures exactly (not merely as a subset). -/
theorem faithful_auxiliary_closureAt_image
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (a : W) :
    B.closureAtSet (f a) = f '' B.closureAtSet a := by
  rw [
    faithful_auxiliary_closureAt_eq_successors
      G k S B ι hFaith (f a),
    faithful_auxiliary_closureAt_eq_successors
      G k S B ι hFaith a]
  have hmap :=
    Structure.Automorphism.map_func f AuxiliaryFunc.successor ![a]
  have htup : (f ∘ ![a]) = ![f a] := by
    funext i
    fin_cases i
    rfl
  rw [htup] at hmap
  have heq :
      f '' B.func AuxiliaryFunc.successor ![a] =
        B.func AuxiliaryFunc.successor ![f a] := by
    simpa only [Structure.imageSet, auxiliaryAction_on_successor] using hmap
  exact heq.symm

/-- All canonical root supports are precisely equivariant under the
induced actual permutation of reconstructed vertices. -/
theorem faithful_reconstructedSupport_map
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (z : ReconstructedCarrier G k B) :
    reconstructedSupport G k B
      (reconstructedVertexPerm G k B f z) =
      f '' reconstructedSupport G k B z := by
  cases z with
  | inl a =>
      change B.closureAtSet (f a) = f '' B.closureAtSet a
      exact faithful_auxiliary_closureAt_image G k S B ι hFaith f a
  | inr p =>
      rfl

end AllThoseEPPA.Applications.KOrientations
