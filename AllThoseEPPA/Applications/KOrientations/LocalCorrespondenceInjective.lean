import AllThoseEPPA.Applications.KOrientations.CommonMoveRootRigidity
import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportMonotone

/-!
# Choice-free local correspondence c_f

Fix a second-stage automorphism f. Its genuine B₀-language component
determines a canonical projection on nonroots (x,W), while f itself
determines the images of root-sort vertices.

The local domain consists exactly of reconstructed vertices whose
ENTIRE intrinsic support is mapped by f into the original root-sort
copy. For root-sort vertices this condition gives the unique source
root corresponding to f(a), and for nonroots it allows us to use
the common-move support rigidity theorem.

The key Claim P1 of the paper says c_f is injective on this domain.
We prove this without quotient representatives or assumptions of
global rootedness of B₀. Preservation/reflection of edges and d-
functions are separate later obligations.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The domain condition for the intrinsic local correspondence. -/
def IsMovedSupport
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (z : ReconstructedCarrier G k B) : Prop :=
  ∀ w ∈ reconstructedSupport G k B z,
    ∃ t : RootsIn G k S, f w = ι t

/-- The exact locally mapped carrier under a fixed B₁ automorphism. -/
abbrev LocalReconstructedCarrier
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :=
  {z : ReconstructedCarrier G k B // IsMovedSupport G k S B ι f z}

/-- The intrinsic, choice-free local correspondence c_f to B₀.

For roots we uniquely invert the root-sort embedding after f;
for nonroots we apply the actual B₀ automorphism obtained by the
exact language correction ι.lang⁻¹ * f.lang. -/
noncomputable def localCorrespondence
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    LocalReconstructedCarrier G k S B ι f → V := by
  classical
  intro z
  obtain ⟨z, hz⟩ := z
  cases z with
  | inl a =>
      exact (Classical.choose (hz a (B.mem_closureAtSet a))).val
  | inr p =>
      exact (ι.lang⁻¹ * f.lang : G.graphAut).1 p.center

/-- An actual witness of the root component of the correspondence. -/
private theorem localCorrespondence_root_witness
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (a : W)
    (ha : IsMovedSupport G k S B ι f (.inl a)) :
    ∃ t : RootsIn G k S,
      f a = ι t ∧
      localCorrespondence G k S B ι f ⟨.inl a, ha⟩ = t.val := by
  classical
  let t : RootsIn G k S :=
    Classical.choose (ha a (B.mem_closureAtSet a))
  refine ⟨t, Classical.choose_spec _, ?_⟩
  rfl

/-- Claim P1, the local correspondence is injective on its entire
support-moved domain. The difficult nonroot/nonroot case follows
from common-move rigidity and does NOT assume nested supports. -/
theorem localCorrespondence_injective
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    Function.Injective (localCorrespondence G k S B ι f) := by
  classical
  intro z t hEq
  obtain ⟨z, hz⟩ := z
  obtain ⟨t, ht⟩ := t
  apply Subtype.ext
  cases z with
  | inl a =>
      cases t with
      | inl b =>
          obtain ⟨ra, ha, hra⟩ :=
            localCorrespondence_root_witness G k S B ι f a hz
          obtain ⟨rb, hb, hrb⟩ :=
            localCorrespondence_root_witness G k S B ι f b ht
          have hr : ra = rb := by
            apply Subtype.ext
            exact hra.symm.trans (hEq.trans hrb)
          have hf : f a = f b := by
            calc
              f a = ι ra := ha
              _ = ι rb := congrArg ι hr
              _ = f b := hb.symm
          exact congrArg Sum.inl (f.toEquiv.injective hf)
      | inr q =>
          obtain ⟨ra, _, hra⟩ :=
            localCorrespondence_root_witness G k S B ι f a hz
          have hr : G.IsRoot k
              ((ι.lang⁻¹ * f.lang : G.graphAut).1 q.center) := by
            rw [← hra, ← hEq]
            exact ra.property.2
          have hq : G.IsRoot k q.center :=
            (G.graphAut_root_iff k
              (ι.lang⁻¹ * f.lang : G.graphAut) q.center).mp hr
          exact False.elim (q.center_nonroot hq)
  | inr p =>
      cases t with
      | inl b =>
          obtain ⟨rb, _, hrb⟩ :=
            localCorrespondence_root_witness G k S B ι f b ht
          have hr : G.IsRoot k
              ((ι.lang⁻¹ * f.lang : G.graphAut).1 p.center) := by
            rw [← hrb, hEq]
            exact rb.property.2
          have hp : G.IsRoot k p.center :=
            (G.graphAut_root_iff k
              (ι.lang⁻¹ * f.lang : G.graphAut) p.center).mp hr
          exact False.elim (p.center_nonroot hp)
      | inr q =>
          have hc : p.center = q.center := by
            apply (ι.lang⁻¹ * f.lang : G.graphAut).1.injective
            exact hEq
          have hpq : p = q :=
            canonicalNonroot_eq_of_common_move
              G k S B ι f p q hc hz ht
          exact congrArg Sum.inr hpq

end AllThoseEPPA.Applications.KOrientations
