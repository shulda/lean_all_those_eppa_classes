import AllThoseEPPA.FaithfulInducedPartialIso
import AllThoseEPPA.FaithfulEmbeddingInverse
import AllThoseEPPA.TreeLikeEmbeddingRangeClosure

/-!
# The canonical interface partial automorphism for two copies of C inside A

For the free-amalgamation induction in manuscript Lemma
`lem:infinitecopies`, an interface C sits in two full copies of A via
Γ-embeddings δ₁ and δ₂. These embeddings canonically determine a
partial automorphism of A mapping δ₁(c) to δ₂(c).

The correct Γ-language component is δ₂.lang * δ₁.lang⁻¹,
not necessarily the identity. We construct the map concretely:
invert δ₁ on its closed image, compose with δ₂, then use the
already checked induced-substructure-to-partial-automorphism bridge.

The construction makes no finiteness, unarity, or trivial-action
assumptions, and function-value fibres are preserved exactly.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {V : Type x}

/-- The closed support of a Γ-embedding of an interface into A. -/
def interfaceSource
    (act : L.Action Γ)
    {C : Structure L I} {A : Structure L V}
    (δ₁ : Structure.Embedding act C A) : Set V :=
  Set.range δ₁.toFun

/-- Given two Γ-embeddings of the same interface C into A,
construct a genuine Γ-partial automorphism of A carrying
δ₁(c) to δ₂(c). -/
noncomputable def interfacePartialAutomorphism
    (act : L.Action Γ)
    {C : Structure L I} {A : Structure L V}
    (δ₁ δ₂ : Structure.Embedding act C A) :
    Structure.PartialAutomorphism act A := by
  let S : Set V := interfaceSource act δ₁
  let hS : A.IsClosed S := δ₁.range_isClosed act
  let back : Structure.Embedding act (A.induce S hS) C :=
    Faithful.embeddingInverseOnClosedSubset
      act δ₁ S hS (by intro x hx; exact hx)
  let move : Structure.Embedding act (A.induce S hS) A :=
    δ₂.comp back
  exact Faithful.partialAutomorphismOfInducedEmbedding
    act A S hS move

/-- The source of the canonical interface partial automorphism
is exactly δ₁(C), even when the two embeddings have different
Γ-language components. -/
@[simp] theorem interfacePartialAutomorphism_source
    (act : L.Action Γ)
    {C : Structure L I} {A : Structure L V}
    (δ₁ δ₂ : Structure.Embedding act C A) :
    (interfacePartialAutomorphism act δ₁ δ₂).source =
      Set.range δ₁.toFun := rfl

/-- Its language part is the correctly conjugated interface
permutation δ₂.lang * δ₁.lang⁻¹. -/
@[simp] theorem interfacePartialAutomorphism_lang
    (act : L.Action Γ)
    {C : Structure L I} {A : Structure L V}
    (δ₁ δ₂ : Structure.Embedding act C A) :
    (interfacePartialAutomorphism act δ₁ δ₂).lang =
      δ₂.lang * δ₁.lang⁻¹ := rfl

/-- On each interface point, the canonical partial automorphism
takes its image in the first A-copy to its image in the second. -/
theorem interfacePartialAutomorphism_apply
    (act : L.Action Γ)
    {C : Structure L I} {A : Structure L V}
    (δ₁ δ₂ : Structure.Embedding act C A) (c : I) :
    interfacePartialAutomorphism act δ₁ δ₂ (δ₁ c) = δ₂ c := by
  classical
  let S : Set V := interfaceSource act δ₁
  let hS : A.IsClosed S := δ₁.range_isClosed act
  let hsub : S ⊆ Set.range δ₁.toFun := fun _ h => h
  let back : Structure.Embedding act (A.induce S hS) C :=
    Faithful.embeddingInverseOnClosedSubset act δ₁ S hS hsub
  let move : Structure.Embedding act (A.induce S hS) A :=
    δ₂.comp back
  have hc : δ₁ c ∈ S := ⟨c, rfl⟩
  have hback : back ⟨δ₁ c, hc⟩ = c := by
    apply δ₁.injective
    exact Faithful.embeddingInverseOnClosedSubset_apply_spec
      act δ₁ S hS hsub ⟨δ₁ c, hc⟩
  change Faithful.partialAutomorphismOfInducedEmbedding
    act A S hS move (δ₁ c) = δ₂ c
  rw [Faithful.partialAutomorphismOfInducedEmbedding_apply
    act A S hS move hc]
  change δ₂ (back ⟨δ₁ c, hc⟩) = δ₂ c
  rw [hback]

end TreeLike
end AllThoseEPPA
