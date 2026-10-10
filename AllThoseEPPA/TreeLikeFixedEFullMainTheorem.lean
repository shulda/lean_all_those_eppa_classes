import AllThoseEPPA.TreeLikeTowerGlobalProjection
import AllThoseEPPA.FaithfulProposition
import AllThoseEPPA.TreeLikeFixedEAllSmallSubstructures

/-!
# Fixed-E restricted EPPA from an arbitrary initial EPPA witness

The manuscript does not assume that B₀ is faithful or coherent.
The already formalized faithful valuation construction first
converts *any* finite EPPA witness into an irreducible-structure
faithful witness B₁, accompanied by an exact homomorphism-
embedding B₁ → B₀.

Iterating the actual sparsening tower over B₁ preserves
finite EPPA and faithfulness, and the canonical composite
of tower projections yields a global homomorphism-embedding
B → B₁. Composing these genuine maps recovers B → B₀.

The local full-A-tree property, including the empty
substructure, follows from the bounded tower theorem.
If B₀ was coherent, the faithful step and every sparsening
stage preserve coherent EPPA as well. No extra coherence
assumption is required for ordinary EPPA.

The only remaining difference from the unrestricted paper
statement is the requirement that a fixed complete relation
E is *already* present in the language.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α β : Type (max u v)}
variable [Finite α] [Finite β]

/-- Full fixed-E form of the restricted EPPA construction:
from any finite EPPA witness, produce a faithful EPPA witness
with global homomorphism-embedding to the original, local
homomorphism-embeddings into trees of full A-copies for all
small closed substructures, and optional coherence. -/
theorem fixedE_restrictedEPPA_from_any_witness
    (act : L.Action Γ)
    (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (B₀ : Structure L β)
    (ψ : Structure.Embedding act A B₀)
    (hEPPA : Structure.IsEPPAWitness act ψ)
    (n : ℕ) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
        (B : Structure L δ)
        (ι : Structure.Embedding act A B),
      Structure.IsEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι ∧
      (∃ f : Structure.Homomorphism act B B₀,
        Structure.Homomorphism.IsHomomorphismEmbedding act f) ∧
      (∀ (S : Set δ) (hS : B.IsClosed S),
        S.ncard ≤ n →
          ∃ (W : Type (max u v)) (H : Structure L W),
            TreeAmalgamation act A H ∧
              ∃ f : Structure.Homomorphism act (B.induce S hS) H,
                Structure.Homomorphism.IsHomomorphismEmbedding act f) ∧
      (Structure.IsCoherentEPPAWitness act ψ →
        Structure.IsCoherentEPPAWitness act ι) := by
  classical
  obtain ⟨hFinite, hEPPA₁, hFaithful₁, hProjection₁, hCoh₁⟩ :=
    Faithful.faithfulWitness_proposition act A B₀ ψ hEPPA
  letI : Finite (Faithful.WitnessVertex act A B₀ ψ) := hFinite
  let B₁ : Structure L (Faithful.WitnessVertex act A B₀ ψ) :=
    Faithful.witnessStructure act A B₀ ψ
  let ψ₁ : Structure.Embedding act A B₁ :=
    Faithful.canonicalEmbedding act A B₀ ψ
  let s : FaithfulSparseningStage act A :=
    FaithfulSparseningStage.initial act A B₁ ψ₁ hEPPA₁ hFaithful₁
  let N := n * (n*n+1)
  let t : FaithfulSparseningStage act A :=
    FaithfulSparseningStage.iterate act A E hfix hcomplete s N
  let p : Structure.Homomorphism act t.model B₀ :=
    (Faithful.projection act A B₀ ψ).comp
      (FaithfulSparseningStage.iterateProjectionToInitial
        act A E hfix hcomplete s N)
  have hp : Structure.Homomorphism.IsHomomorphismEmbedding act p :=
    Structure.Homomorphism.comp_isHomomorphismEmbedding
      act (Faithful.projection act A B₀ ψ)
      (FaithfulSparseningStage.iterateProjectionToInitial
        act A E hfix hcomplete s N)
      hProjection₁
      (FaithfulSparseningStage.iterateProjectionToInitial_isHomomorphismEmbedding
        act A E hfix hcomplete s N)
  refine ⟨t.Carrier, t.finiteCarrier, t.model, t.embedding,
    t.isEPPA, t.isFaithful, ⟨p, hp⟩, ?_, ?_⟩
  · intro S hS hBound
    by_cases hNonempty : S.Nonempty
    · let T : ClosedStageSubset act A t := ⟨S, hS⟩
      exact ClosedStageSubset.bounded_tower_homomorphismEmbeds_into_fullATree
        act A E hfix hcomplete s n T hNonempty hBound
    · have hEmpty : S = (∅ : Set t.Carrier) := by
        ext x
        constructor
        · intro hx
          exact (hNonempty ⟨x, hx⟩).elim
        · intro hx
          exact hx.elim
      subst S
      obtain ⟨W, H, hTree, ⟨e⟩⟩ :=
        emptyInduced_embedsFullATree act A t.model t.embedding
      refine ⟨W, H, hTree, e.toHomomorphism, ?_⟩
      intro T hT hIrr
      refine ⟨?_, ?_, ?_⟩
      · intro a ha b hb hab
        exact e.injective hab
      · intro m R xs hxs
        exact e.map_rel_iff R xs
      · intro m F xs hxs
        exact e.map_func F xs
  · intro hCoherent
    exact FaithfulSparseningStage.iterate_coherent
      act A E hfix hcomplete s (hCoh₁ hCoherent) N

end TreeLike
end AllThoseEPPA
