import AllThoseEPPA.Applications.KOrientations.AuxiliaryClosedRootCoherentComposition

/-!
# Compose ACTUAL image equalities and coherent auxiliary root partial maps

The closed-domain Γ-partial-isomorphism theorem requires the
first-stage B₀ graph automorphism g to map the selected original
d-closed source domain T exactly onto the target T'. It does not
require g to preserve the whole original subset S.

For two composable first-stage automorphisms g, h, such
equality for T₁→T₂ and T₂→T₃ automatically implies the exact
equality for their product h*g and T₁→T₃. Thus the existing
coherent-triple lemma can be instantiated WITHOUT a third
independently assumed domain-image identity, and the resulting
group component is literally the multiplication in Aut(B₀).

This records the precise second-stage coherence input needed
for the reconstructed k-orientation extension, without asserting
existence of the final coherent EPPA witness yet.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- The product of actual B₀ graph automorphisms transports
the complete original closed source domain onto the complete
target domain. No global invariance of S is assumed. -/
theorem auxiliaryClosedRootDomain_image_comp
    {V : Type u} [Fintype V] (G : Digraph V)
    (S : Set V) (T₁ T₂ T₃ : Set S)
    (g h : G.graphAut)
    (hg : g.1 '' (Subtype.val '' T₁) = Subtype.val '' T₂)
    (hh : h.1 '' (Subtype.val '' T₂) = Subtype.val '' T₃) :
    (h * g).1 '' (Subtype.val '' T₁) =
      Subtype.val '' T₃ := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hgZ : g.1 z ∈ Subtype.val '' T₂ := by
      rw [← hg]
      exact ⟨z, hz, rfl⟩
    rw [← hh]
    refine ⟨g.1 z, hgZ, ?_⟩
    simp
  · intro hx
    rw [← hh] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    rw [← hg] at hw
    obtain ⟨z, hz, hzw⟩ := hw
    refine ⟨z, hz, ?_⟩
    change h.1 (g.1 z) = x
    rw [hzw]
    exact hwx

/-- The exact auxiliary Γ-root partial isomorphisms of any two
consecutive original d-closed source-domain maps form a genuine
coherent triple, with NO extra composite-domain hypothesis. -/
theorem auxiliaryClosedRootPartialIsomorphism_coherentTriple_of_images
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T₁ T₂ T₃ : Set S)
    (hT₁ : (dTraceStructure G k S).IsClosed T₁)
    (hT₂ : (dTraceStructure G k S).IsClosed T₂)
    (hT₃ : (dTraceStructure G k S).IsClosed T₃)
    (g h : G.graphAut)
    (hg : g.1 '' (Subtype.val '' T₁) = Subtype.val '' T₂)
    (hh : h.1 '' (Subtype.val '' T₂) = Subtype.val '' T₃) :
    Structure.PartialIsomorphism.CoherentTriple
      (auxiliaryClosedRootPartialIsomorphism
        G k S T₁ T₂ hT₁ hT₂ g hg)
      (auxiliaryClosedRootPartialIsomorphism
        G k S T₂ T₃ hT₂ hT₃ h hh)
      (auxiliaryClosedRootPartialIsomorphism
        G k S T₁ T₃ hT₁ hT₃ (h * g)
          (auxiliaryClosedRootDomain_image_comp G S T₁ T₂ T₃ g h hg hh)) := by
  exact auxiliaryClosedRootPartialIsomorphism_coherentTriple
    G k S T₁ T₂ T₃ hT₁ hT₂ hT₃ g h hg hh
    (auxiliaryClosedRootDomain_image_comp G S T₁ T₂ T₃ g h hg hh)

end AllThoseEPPA.Applications.KOrientations
