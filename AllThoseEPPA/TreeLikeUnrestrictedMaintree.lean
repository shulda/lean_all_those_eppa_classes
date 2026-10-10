import AllThoseEPPA.TreeLikeFixedEFullMainTheorem
import AllThoseEPPA.TreeLikeFreshBinaryComplete
import AllThoseEPPA.TreeLikeFreshBinaryWitnessReduct
import AllThoseEPPA.TreeLikeFreshBinaryTreeReduct

/-!
# Unrestricted locally tree-like EPPA construction (thm:maintree)

The complete proof is the verified fixed-E construction together with
the explicit fresh relation expansion/reduct transports:

* Add a new binary E fixed by all Γ-symbol permutations, complete on A
  and the initial witness B₀. Existing relations and unary functions
  are unchanged.
* Lift the initial ordinary EPPA witness and its optional coherence.
* Apply the finite, bounded cycle-sparsening and faithful fixed-E
  construction, yielding a homomorphism-embedding back to B₀ and
  real homomorphism-embeddings from each small closed substructure
  into an explicit tree amalgamation of full expanded A-copies.
* Forget E. The exact map and faithful EPPA witness descend, as do
  every coherent extension and every literal full-A tree amalgamation.

No completeness hypothesis on E in the *output* expanded witness is
assumed: its E relation is sparsified by the construction.
The numerical bound uses N=n*(n*n+1), counting ordered edge pairs.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α β : Type (max u v)} [Finite α] [Finite β]

/-- Full unrestricted form of manuscript Theorem thm:maintree.

From any finite Γ-EPPA witness B₀ of A in a unary-function language,
construct a finite irreducible-structure faithful EPPA witness B.
It admits a global homomorphism-embedding B→B₀, and every closed
substructure on at most n vertices admits a homomorphism-embedding
into a recursive tree amalgamation of full copies of the *original*
A (without the auxiliary relation E). If B₀ is coherent, so is B.

In particular no distinguished binary relation is assumed in L. -/
theorem restrictedEPPA_from_any_witness
    (act : L.Action Γ)
    (A : Structure L α)
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
  let Aplus : Structure L.withFixedBinaryRel α :=
    A.withCompleteFixedBinary
  let B₀plus : Structure L.withFixedBinaryRel β :=
    B₀.withCompleteFixedBinary
  let actPlus : L.withFixedBinaryRel.Action Γ :=
    act.withFixedBinaryRel
  let ψplus : Structure.Embedding actPlus Aplus B₀plus :=
    ψ.withCompleteFixedBinary act
  have hFix : actPlus.FixesRel
      (Language.withFixedBinaryRel.freshE L) :=
    Language.Action.withFixedBinaryRel_fixesFresh act
  have hComplete : Aplus.EdgeComplete
      (Language.withFixedBinaryRel.freshE L) :=
    Structure.withCompleteFixedBinary_edgeComplete A
  have hEPPAplus : Structure.IsEPPAWitness actPlus ψplus :=
    Structure.isEPPAWitness_withCompleteFixedBinary act ψ hEPPA
  obtain ⟨δ, hδ, Bplus, ιplus, hEPPAout, hFaithout,
      ⟨pplus, hpplus⟩, hSmallPlus, hOptional⟩ :=
    fixedE_restrictedEPPA_from_any_witness
      actPlus Aplus (Language.withFixedBinaryRel.freshE L)
      hFix hComplete B₀plus ψplus hEPPAplus n
  let B : Structure L δ := Bplus.forgetFixedBinary
  let ι : Structure.Embedding act A B :=
    ιplus.forgetFixedBinary act
  refine ⟨δ, hδ, B, ι, ?_, ?_, ?_, ?_, ?_⟩
  · exact Structure.isEPPAWitness_forgetFixedBinary_of_complete_source
      act ιplus hEPPAout
  · exact Structure.isIrreducibleStructureFaithful_forgetFixedBinary
      act ιplus hFaithout
  · exact ⟨pplus.forgetFixedBinary act,
      Structure.Homomorphism.forgetFixedBinary_isHomomorphismEmbedding
        act pplus hpplus⟩
  · intro S hS hBound
    have hSplus : Bplus.IsClosed S := hS
    obtain ⟨W, Hplus, hTreePlus, ⟨fplus, hfplus⟩⟩ :=
      hSmallPlus S hSplus hBound
    refine ⟨W, Hplus.forgetFixedBinary, ?_, ?_⟩
    · exact TreeAmalgamation.forgetFixedBinary
        act Aplus Hplus hTreePlus
    · exact ⟨fplus.forgetFixedBinary act,
        Structure.Homomorphism.forgetFixedBinary_isHomomorphismEmbedding
          act fplus hfplus⟩
  · intro hCoh
    have hCohPlus : Structure.IsCoherentEPPAWitness actPlus ψplus :=
      Structure.isCoherentEPPAWitness_withCompleteFixedBinary
        act ψ hCoh
    exact Structure.isCoherentEPPAWitness_forgetFixedBinary_of_complete_source
      act ιplus (hOptional hCohPlus)

end TreeLike
end AllThoseEPPA
