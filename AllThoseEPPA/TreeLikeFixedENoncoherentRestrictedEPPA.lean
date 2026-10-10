import AllThoseEPPA.TreeLikeFixedEAllSmallSubstructures

/-!
# Restricted EPPA without a coherence hypothesis

The construction in manuscript thm:maintree starts from an
arbitrary EPPA witness, not necessarily a coherent one.
The finite sparsening tower preserves EPPA without coherence;
coherence is an additional property preserved if already
available. This module formalizes the independent,
noncoherent fixed-E result, retaining every closed small
substructure including the empty one.

The starting witness is assumed irreducible-structure faithful.
Removing that assumption requires the already formalized
faithfulness construction and its projection.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α β : Type (max u v)}
variable [Finite α] [Finite β]

/-- Fixed-E restricted EPPA from any finite *faithful* EPPA
witness, whether or not a coherent extension is supplied.
Every closed substructure on at most n vertices has a real
Γ-homomorphism-embedding into a tree of full copies of A. -/
theorem fixedE_faithful_restrictedEPPA_all
    (act : L.Action Γ)
    (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (B₀ : Structure L β)
    (ψ : Structure.Embedding act A B₀)
    (hEPPA : Structure.IsEPPAWitness act ψ)
    (hFaithful : Structure.IsIrreducibleStructureFaithful act ψ)
    (n : ℕ) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
        (B : Structure L δ)
        (ι : Structure.Embedding act A B),
      Structure.IsEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι ∧
      ∀ (S : Set δ) (hS : B.IsClosed S),
        S.ncard ≤ n →
          ∃ (W : Type (max u v)) (H : Structure L W),
            TreeAmalgamation act A H ∧
              ∃ f : Structure.Homomorphism act (B.induce S hS) H,
                Structure.Homomorphism.IsHomomorphismEmbedding act f := by
  classical
  let s : FaithfulSparseningStage act A :=
    FaithfulSparseningStage.initial act A B₀ ψ hEPPA hFaithful
  let N := n * (n*n+1)
  let t : FaithfulSparseningStage act A :=
    FaithfulSparseningStage.iterate act A E hfix hcomplete s N
  refine ⟨t.Carrier, t.finiteCarrier, t.model,
    t.embedding, t.isEPPA, t.isFaithful, ?_⟩
  intro S hS hBound
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

end TreeLike
end AllThoseEPPA
