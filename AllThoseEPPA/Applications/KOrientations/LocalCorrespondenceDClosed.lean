import AllThoseEPPA.Applications.KOrientations.LocalCorrespondenceReachability
import AllThoseEPPA.Applications.KOrientations.Closures

/-!
# Full d-closure of the support-moved local domain

The local correspondence is defined exactly on reconstructed vertices
whose entire intrinsic support is transported into the original source
root sort by one fixed auxiliary automorphism f.

The checked antitonicity argument already gives successor-closedness.
Under the explicit and still-to-be-established identity
  reachableRoots(z) = tagged intrinsicSupport(z),
this domain is also closed under *every* root-fibre function F_n.

Indeed, an element of F_n has support consisting precisely of the
input root vertices. Every input root in the moved domain contains
itself in its unary auxiliary closure, so its singleton is moved too.

This proves conditional d-closedness without assuming the final EPPA
conclusion, surjectivity of the local map, or any bound on root arity.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- With exact reachable-root supports, the support-moved domain is
closed under both directed reachability and every root-fibre operation
of the full d-language. -/
theorem isMovedSupport_set_isDClosed_of_exact_roots
    {V : Type u} [Fintype V] {W : Type v} [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (hRoots : ∀ z : ReconstructedCarrier G k B,
      (faithfulReconstructedDigraph G k S B ι hFaith).roots k z =
        (Sum.inl : W → ReconstructedCarrier G k B) ''
          reconstructedSupport G k B z) :
    (faithfulReconstructedDigraph G k S B ι hFaith).IsDClosed
      k {z | IsMovedSupport G k S B ι f z} := by
  constructor
  · intro x y hx hxy
    exact isMovedSupport_of_reconstructed_reaches
      G k S B ι hFaith f hx hxy
  · intro n xs hxs z hz
    intro w hw
    have hRoot :
        (Sum.inl w : ReconstructedCarrier G k B) ∈
          (faithfulReconstructedDigraph G k S B ι hFaith).roots k z := by
      rw [hRoots z]
      exact ⟨w, hw, rfl⟩
    have hRange :=
      (faithfulReconstructedDigraph G k S B ι hFaith).roots_eq_range_of_mem_dFiber
        k hz
    rw [hRange] at hRoot
    obtain ⟨i, hi⟩ := hRoot
    have hSelf :
        w ∈ reconstructedSupport G k B (xs i) := by
      rw [hi]
      exact B.mem_closureAtSet w
    exact hxs i w hSelf

end AllThoseEPPA.Applications.KOrientations
