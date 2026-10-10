import AllThoseEPPA.StrongCompletionSmallTrees
import AllThoseEPPA.TreeLikeUnrestrictedMaintree
import AllThoseEPPA.TreeLikeFaithfulEmbeddingBridge

/-!
# The locally finite strong-completion step

This is the core constructive implication behind manuscript
Theorem 1.6, for a fixed source A and starting EPPA witness B₀.

Given the *ordinary* local-small-completion condition of
Definition 11.2 and an automorphism-preserving completion promised
under that condition, the checked restricted tree-like EPPA theorem
provides a finite intermediate B₁.

Observation 9.4 upgrades its local full-A trees into ordinary
completions in K; irreducible-structure faithfulness yields the
required embeddings of all irreducible B₁-substructures into A.

The local finiteness hypothesis then supplies an
automorphism-preserving strong completion of B₁. As A is
irreducible, its distinguished embedding into B₁ remains an
exact embedding into the completion *automatically*. The
earlier verified automorphism transport gives ordinary and
optionally coherent EPPA.

The substantive local finiteness condition is stated explicitly
rather than smuggled into the theorem as a completion of B₁.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α β : Type (max u v)} [Finite α] [Finite β]

/-- A fixed-(A,B₀) instance of the exact local finiteness
condition, with an automorphism-preserving strong completion as
conclusion. The small-piece assumption is **ordinary**
completion, precisely as in manuscript Definition 11.2. -/
def HasLocallyFiniteAutomorphismPreservingCompletion
    (act : L.Action Γ)
    (A : Structure L α)
    (B₀ : Structure L β)
    (K : FiniteAmalgamationClass act) : Prop :=
  ∃ n : ℕ,
    ∀ {δ : Type (max u v)} [Finite δ]
      (B : Structure L δ),
      EveryIrreducibleEmbedsIn act A B →
      (∃ p : Structure.Homomorphism act B B₀,
        Structure.Homomorphism.IsHomomorphismEmbedding act p) →
      (∀ (S : Set δ) (hS : B.IsClosed S),
        S.ncard ≤ n → K.HasCompletion (B.induce S hS)) →
      ∃ (Z : Type (max u v)) (_ : Finite Z)
          (C : Structure L Z),
        K.mem C ∧
        Nonempty (Structure.AutomorphismPreservingStrongCompletion act B C)

/-- Locally finite automorphism-preserving classes inherit
ordinary and optional coherent EPPA along one fixed input witness.

In particular the proof does not invoke Proposition 11.3:
ordinary small completions suffice for the exact Definition 11.2
predicate above. -/
theorem restrictedEPPA_inLocallyFiniteClass
    (act : L.Action Γ)
    (A : Structure L α) (hIrr : A.IsIrreducible)
    (K : FiniteAmalgamationClass act) (hKA : K.mem A)
    (B₀ : Structure L β)
    (ψ : Structure.Embedding act A B₀)
    (hEPPA : Structure.IsEPPAWitness act ψ)
    (hLocal :
      HasLocallyFiniteAutomorphismPreservingCompletion act A B₀ K) :
    ∃ (Z : Type (max u v)) (_ : Finite Z)
        (C : Structure L Z)
        (ι : Structure.Embedding act A C),
      K.mem C ∧
      Structure.IsEPPAWitness act ι ∧
      (Structure.IsCoherentEPPAWitness act ψ →
        Structure.IsCoherentEPPAWitness act ι) := by
  classical
  obtain ⟨n, hLocalN⟩ := hLocal
  obtain ⟨δ, hδ, B, ι, hEPPAB, hFaithfulB,
      hProjection, hSmallTrees, hCoherentB⟩ :=
    restrictedEPPA_from_any_witness act A B₀ ψ hEPPA n
  letI : Finite δ := hδ
  have hEvery : EveryIrreducibleEmbedsIn act A B :=
    everyIrreducibleEmbedsIn_of_faithful
      act A B ι hFaithfulB
  have hSmallComplete :
      ∀ (S : Set δ) (hS : B.IsClosed S),
        S.ncard ≤ n → K.HasCompletion (B.induce S hS) :=
    smallClosedTrees_haveCompletions
      act A hIrr K hKA B n hSmallTrees
  obtain ⟨Z, hZ, C, hKC, ⟨c⟩⟩ :=
    hLocalN B hEvery hProjection hSmallComplete
  let ιC : Structure.Embedding act A C :=
    c.completedEmbedding ι hIrr
  refine ⟨Z, hZ, C, ιC, hKC, ?_, ?_⟩
  · exact c.preservesEPPA_of_irreducible ι hIrr hEPPAB
  · intro hCoherent0
    exact c.preservesCoherentEPPA_of_irreducible
      ι hIrr (hCoherentB hCoherent0)

end TreeLike
end AllThoseEPPA
