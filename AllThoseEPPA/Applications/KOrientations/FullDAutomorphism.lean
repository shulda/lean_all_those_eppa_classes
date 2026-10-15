import AllThoseEPPA.Applications.KOrientations.ReconstructedDAutomorphismEmbedding
import AllThoseEPPA.EPPA
import Mathlib.Logic.Equiv.PartialEquiv

/-!
# From bijective exact embeddings to genuine total automorphisms

The public EPPA API represents total automorphisms by partial
isomorphisms with source and target equal to the entire carrier.
A bijective embedding of a structure in itself provides exactly such
an object via `Equiv.toPartialEquiv`.

Applying this conversion to the already proved canonical action of
the second-stage B₁ automorphism group yields genuine automorphisms
of the reconstructed complete d-language, not merely permutations
with separately recorded compatibility properties.
-/

namespace AllThoseEPPA

universe u v w

namespace Structure

/-- A bijective endomorphism embedding is a genuine total automorphism
in the public partial-isomorphism EPPA API. -/
noncomputable def Embedding.toAutomorphismOfBijective
    {L : Language.{u}} {Γ : Type v} [Group Γ]
    {V : Type w} {A : Structure L V}
    {act : L.Action Γ}
    (e : Embedding act A A)
    (he : Function.Bijective e.toFun) :
    Automorphism act A := by
  let eqv : V ≃ V := Equiv.ofBijective e.toFun he
  refine {
    toPartialIsomorphism := {
      lang := e.lang
      toPartialEquiv := eqv.toPartialEquiv
      source_closed := ?_
      target_closed := ?_
      map_rel_iff := ?_
      map_func := ?_ }
    source_eq_univ := ?_
    target_eq_univ := ?_ }
  · simpa only [Equiv.toPartialEquiv_source] using A.isClosed_univ
  · simpa only [Equiv.toPartialEquiv_target] using A.isClosed_univ
  · intro n R xs _
    change A.rel (act.onRel e.lang R) (e.toFun ∘ xs) ↔ A.rel R xs
    exact e.map_rel_iff R xs
  · intro n F xs _
    change imageSet e.toFun (A.func F xs) =
      A.func (act.onFunc e.lang F) (e.toFun ∘ xs)
    exact e.map_func F xs
  · exact Equiv.toPartialEquiv_source eqv
  · exact Equiv.toPartialEquiv_target eqv

end Structure

namespace Applications.KOrientations

/-- The canonical reconstructed B₁-action now yields actual
`Structure.Automorphism` objects in the full d-language. -/
noncomputable def faithful_reconstructed_dAutomorphism_of_auxAutomorphism
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    Structure.Automorphism dTrivialAction
      (dStructure (faithfulReconstructedDigraph G k S B ι hFaith) k) :=
  (faithful_reconstructed_dEmbedding_of_auxAutomorphism
    G k S B ι hFaith f).toAutomorphismOfBijective
      (faithful_reconstructed_dEmbedding_of_auxAutomorphism_bijective
        G k S B ι hFaith f)

/-- The total d-automorphism has exactly the original choice-free
coordinatewise vertex action, on both reconstructed sorts. -/
theorem faithful_reconstructed_dAutomorphism_apply
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (z : ReconstructedCarrier G k B) :
    faithful_reconstructed_dAutomorphism_of_auxAutomorphism
      G k S B ι hFaith f z =
      reconstructedVertexPerm G k B f z := by
  rfl

end Applications.KOrientations
end AllThoseEPPA
