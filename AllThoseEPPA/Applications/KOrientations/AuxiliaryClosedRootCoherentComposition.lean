import AllThoseEPPA.Applications.KOrientations.AuxiliaryRootPartialIsomorphism

/-!
# Coherent composition of true induced auxiliary root partial isomorphisms

A graph automorphism of the first-stage witness generally does NOT
preserve the entire original source substructure S. It does,
however, map an actual selected d-closed source domain onto its
selected d-closed target. The resulting Γ-partial isomorphism of
the auxiliary root structure has:
  * exact induced source/target root subtypes,
  * the ORIGINAL graph automorphism as group component,
  * and the same graph automorphism's vertex action on its source.

For successive graph automorphisms g, h with exact image equalities
T₁ -> T₂ -> T₃, the induced partial isomorphism for h*g is their
coherent composition in the literal public
Structure.PartialIsomorphism.CoherentTriple sense.

The proof uses source-restricted partial equivalences and real
group multiplication. There is no arbitrary totalization outside
the domains, no assumption g[S]=S, and no weakening to mere
positive-atomic homomorphism.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- The true auxiliary root Γ-partial isomorphisms of consecutive
d-closed source/range domains compose COHERENTLY whenever the
actual first-stage B₀ graph automorphisms compose.

The composite source-to-target image equation is kept explicit:
it can be obtained from the two constituent image equations,
and its proof term is irrelevant to the resulting partial map. -/
theorem auxiliaryClosedRootPartialIsomorphism_coherentTriple
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T₁ T₂ T₃ : Set S)
    (hT₁ : (dTraceStructure G k S).IsClosed T₁)
    (hT₂ : (dTraceStructure G k S).IsClosed T₂)
    (hT₃ : (dTraceStructure G k S).IsClosed T₃)
    (g h : G.graphAut)
    (hg : g.1 '' (Subtype.val '' T₁) = Subtype.val '' T₂)
    (hh : h.1 '' (Subtype.val '' T₂) = Subtype.val '' T₃)
    (hhg : (h * g).1 '' (Subtype.val '' T₁) =
      Subtype.val '' T₃) :
    Structure.PartialIsomorphism.CoherentTriple
      (auxiliaryClosedRootPartialIsomorphism
        G k S T₁ T₂ hT₁ hT₂ g hg)
      (auxiliaryClosedRootPartialIsomorphism
        G k S T₂ T₃ hT₂ hT₃ h hh)
      (auxiliaryClosedRootPartialIsomorphism
        G k S T₁ T₃ hT₁ hT₃ (h * g) hhg) := by
  let p := auxiliaryClosedRootPartialIsomorphism
    G k S T₁ T₂ hT₁ hT₂ g hg
  let q := auxiliaryClosedRootPartialIsomorphism
    G k S T₂ T₃ hT₂ hT₃ h hh
  let r := auxiliaryClosedRootPartialIsomorphism
    G k S T₁ T₃ hT₁ hT₃ (h * g) hhg
  have hpq : p.target = q.source := rfl
  refine ⟨hpq, ?_⟩
  refine ⟨rfl, ⟨rfl, ?_⟩⟩
  intro x hx
  have hxU : x ∈ auxiliaryClosedRootDomain G k S T₁ := hx
  have hpU : p x ∈ auxiliaryClosedRootDomain G k S T₂ :=
    p.map_source hx
  have hpx : (p x).val = g.1 x.val :=
    auxiliaryClosedRootPartialEquiv_value
      G k S T₁ T₂ g hg x hxU
  have hqy : (q (p x)).val = h.1 (p x).val :=
    auxiliaryClosedRootPartialEquiv_value
      G k S T₂ T₃ h hh (p x) hpU
  have hrx : (r x).val = (h * g).1 x.val :=
    auxiliaryClosedRootPartialEquiv_value
      G k S T₁ T₃ (h * g) hhg x hxU
  apply Subtype.ext
  change (r x).val = (q (p x)).val
  calc
    (r x).val = (h * g).1 x.val := hrx
    _ = h.1 (g.1 x.val) := by simp
    _ = h.1 (p x).val := congrArg h.1 hpx.symm
    _ = (q (p x)).val := hqy.symm

end AllThoseEPPA.Applications.KOrientations
