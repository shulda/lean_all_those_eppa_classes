import AllThoseEPPA.TreeLikeHomEmbComposition
import AllThoseEPPA.TreeLikeTowerCycleFreeAncestor

/-!
# Actual homomorphism-embedding along a certified projected ancestor

The bounded-rank descent from the **concrete finite
sparsening tower** produces `ProjectedAncestor act A E ... T U`.
That certificate is not merely an inequality between
cardinalities: it records a finite chain of actual
canonical backwards projections between closed substructures.

At every one-step projection the induced map between
these closed substructures is a Γ-homomorphism-embedding,
and the preceding module proves such maps compose.

By induction on the actual `ProjectedAncestor`
certificate, we thus construct a *genuine* homomorphism-
embedding of the chosen top-level substructure into its
cycle-free ancestor. This is precisely what is needed
to compose with the exact embedding into a full-A
tree supplied by `lem:cuts`.

The witness statement stays in `Prop` (an existential
quantifier over actual maps), to avoid invalid elimination
of arbitrary inductive `Prop` proofs into computational
carrier-map data. No oracle or unspecified projection
map is assumed.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w}

/-- Identity homomorphisms are homomorphism-embeddings;
indeed they are exact embeddings on every subset.
This is the base case of a chain of projections. -/
theorem id_isHomomorphismEmbedding
    (act : L.Action Γ) (B : Structure L V) :
    IsHomomorphismEmbedding act (Homomorphism.id (act := act) B) := by
  intro S hS hIrr
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    exact hab
  · intro n R xs hxs
    simp [Homomorphism.id]
  · intro n F xs hxs
    simp [Homomorphism.id, Structure.imageSet]

end Homomorphism
end Structure

namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type (max u v)}

namespace ClosedStageSubset

/-- Every *actual* certified projected ancestor is joined
to the original closed top-level substructure by a genuine
Γ-homomorphism-embedding. It is the composition of precisely
the canonical induced projection maps given by its certificate;
no global injectivity is assumed or required. -/
theorem ProjectedAncestor.exists_homomorphismEmbedding
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    {k : ℕ}
    {T : ClosedStageSubset act A
      (FaithfulSparseningStage.iterate act A E hfix hcomplete s k)}
    {j : ℕ}
    {U : ClosedStageSubset act A
      (FaithfulSparseningStage.iterate act A E hfix hcomplete s (j+1))}
    (h : ProjectedAncestor act A E hfix hcomplete s T U) :
    ∃ f : Structure.Homomorphism act
        ((FaithfulSparseningStage.iterate
          act A E hfix hcomplete s k).model.induce
          T.support T.closed)
        ((FaithfulSparseningStage.iterate
          act A E hfix hcomplete s (j+1)).model.induce
          U.support U.closed),
      Structure.Homomorphism.IsHomomorphismEmbedding act f := by
  induction h with
  | newest T =>
      let C :=
        (FaithfulSparseningStage.iterate
          act A E hfix hcomplete s _).model.induce
          T.support T.closed
      exact ⟨Structure.Homomorphism.id (act := act) C,
        Structure.Homomorphism.id_isHomomorphismEmbedding act C⟩
  | @previous m j T U hAnc ih =>
      obtain ⟨f, hf⟩ := ih
      let sm := FaithfulSparseningStage.iterate
        act A E hfix hcomplete s m
      let p : Structure.Homomorphism act
          ((FaithfulSparseningStage.iterate
            act A E hfix hcomplete s (m+1)).model.induce
            T.support T.closed)
          (sm.model.induce
            (projectAt act A E hfix hcomplete s m T).support
            (projectAt act A E hfix hcomplete s m T).closed) :=
        projectHom act A E hfix hcomplete sm T
      have hp : Structure.Homomorphism.IsHomomorphismEmbedding act p :=
        projectHom_isHomomorphismEmbedding act A E hfix hcomplete sm T
      exact ⟨f.comp p,
        Structure.Homomorphism.comp_isHomomorphismEmbedding
          act f p hf hp⟩

end ClosedStageSubset
end TreeLike
end AllThoseEPPA
