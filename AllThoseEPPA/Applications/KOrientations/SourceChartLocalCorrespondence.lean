import AllThoseEPPA.Applications.KOrientations.SourceChartBijection
import AllThoseEPPA.Applications.KOrientations.LocalCorrespondenceGraph

/-!
# The choice-free local correspondence is inverse to the source chart

For a fixed second-stage automorphism f, the local chart inverse sends
a template source vertex x to the reconstructed copy of x moved back
by f⁻¹. The canonical correspondence c_f must take this vertex
*exactly* to x, not just to a template vertex with the same support.

For roots, this follows from the injectivity of the auxiliary source
embedding. For nonroots, it is the cancellation of the actual graph
automorphism components ι.lang⁻¹, f.lang and f.symm.lang, together with
the exact centre formula for source R_P-patterns.

This is the missing coordinate identity allowing the checked local
induced-graph embedding to be upgraded to an isomorphism onto S.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Root entries of the local correspondence equal any source root
whose image is the transported old vertex. -/
private theorem localCorrespondence_root_of_witness
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (a : W) (ha : IsMovedSupport G k S B ι f (.inl a))
    (t : RootsIn G k S) (ht : f a = ι t) :
    localCorrespondence G k S B ι f ⟨.inl a, ha⟩ = t.val := by
  classical
  change (Classical.choose
    (ha a (B.mem_closureAtSet a))).val = t.val
  have hChoose :=
    Classical.choose_spec (ha a (B.mem_closureAtSet a))
  have hEq :
      (Classical.choose (ha a (B.mem_closureAtSet a))) = t :=
    ι.injective (hChoose.symm.trans ht)
  exact congrArg Subtype.val hEq

/-- For every source vertex, the intrinsic local correspondence
is literally the inverse of the choice-free source chart. -/
theorem localCorrespondence_inverseSourceChart
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (x : {v : V // v ∈ S}) :
    localCorrespondence G k S B ι f
      (inverseSourceChart G k S hClosed hRooted B ι hFaith f x) =
        x.val := by
  classical
  by_cases hx : G.IsRoot k x.val
  · let t : RootsIn G k S := ⟨x.val, x.property, hx⟩
    have hSource :
        sourceReconstructedVertex G k S hClosed hRooted B ι x =
          (.inl (ι t) : ReconstructedCarrier G k B) := by
      simp only [sourceReconstructedVertex, dif_pos hx]
      rfl
    have hVal :
        (inverseSourceChart G k S hClosed hRooted B ι hFaith f x).val =
          (.inl (f.symm (ι t)) : ReconstructedCarrier G k B) := by
      change reconstructedVertexPerm G k B f.symm
        (sourceReconstructedVertex G k S hClosed hRooted B ι x) = _
      rw [hSource]
      rfl
    have hMove :
        IsMovedSupport G k S B ι f (.inl (f.symm (ι t))) := by
      have h := (inverseSourceChart
        G k S hClosed hRooted B ι hFaith f x).property
      rw [hVal] at h
      exact h
    have hChart :
        inverseSourceChart G k S hClosed hRooted B ι hFaith f x =
          ⟨.inl (f.symm (ι t)), hMove⟩ :=
      Subtype.ext hVal
    rw [hChart]
    exact localCorrespondence_root_of_witness
      G k S B ι f (f.symm (ι t)) hMove t
      (Structure.Automorphism.apply_symm_apply f (ι t))
  · let d := chosenSourceNonroot G k S hClosed hRooted
        x.val x.property hx
    let p : CanonicalNonroot G k B := d.toCanonical B ι
    let q : CanonicalNonroot G k B := CanonicalNonroot.map f.symm p
    have hSource :
        sourceReconstructedVertex G k S hClosed hRooted B ι x =
          (.inr p : ReconstructedCarrier G k B) := by
      simp only [sourceReconstructedVertex, dif_neg hx]
      rfl
    have hVal :
        (inverseSourceChart G k S hClosed hRooted B ι hFaith f x).val =
          (.inr q : ReconstructedCarrier G k B) := by
      change reconstructedVertexPerm G k B f.symm
        (sourceReconstructedVertex G k S hClosed hRooted B ι x) = _
      rw [hSource]
      rfl
    have hMove : IsMovedSupport G k S B ι f (.inr q) := by
      have h := (inverseSourceChart
        G k S hClosed hRooted B ι hFaith f x).property
      rw [hVal] at h
      exact h
    have hChart :
        inverseSourceChart G k S hClosed hRooted B ι hFaith f x =
          ⟨.inr q, hMove⟩ :=
      Subtype.ext hVal
    rw [hChart]
    change (ι.lang⁻¹ * f.lang : G.graphAut).1 q.center = x.val
    have hCenter : q.center =
        f.symm.lang.1 (ι.lang.1 x.val) := by
      change (CanonicalNonroot.map f.symm
        (d.toCanonical B ι)).center = _
      rw [CanonicalNonroot.map_center, d.toCanonical_center]
    rw [hCenter]
    have hGroup :
        (ι.lang⁻¹ * f.lang : G.graphAut) * f.symm.lang =
          ι.lang⁻¹ := by
      rw [Structure.Automorphism.symm_lang]
      simp [mul_assoc]
    change (((ι.lang⁻¹ * f.lang : G.graphAut) * f.symm.lang).1
      (ι.lang.1 x.val)) = x.val
    rw [hGroup]
    change (ι.lang.1).symm (ι.lang.1 x.val) = x.val
    exact (ι.lang.1).symm_apply_apply x.val

end AllThoseEPPA.Applications.KOrientations
