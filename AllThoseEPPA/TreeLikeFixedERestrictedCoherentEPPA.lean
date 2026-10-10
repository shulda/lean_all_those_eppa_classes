import AllThoseEPPA.TreeLikeTowerFullTreeHomEmb
import AllThoseEPPA.UnrestrictedFaithfulEPPA

/-!
# Restricted coherent EPPA with a fixed complete E-relation

This packages all already formalized construction stages of
the proof of manuscript Theorem `thm:maintree` in a
language which **already contains** the Γ-fixed binary
relation E and in which E is complete on the distinguished
finite source A.

Given a finite irreducible-structure faithful coherent
EPPA witness B₀ of A, we construct an actual finite
witness by applying the checked cycle-sparsening operation
N=n*(n*n+1) times. Coherent EPPA and irreducible-structure
faithfulness are preserved at each level. For **every
nonempty closed substructure on at most n vertices** of
this explicit final witness, the concrete bounded-rank
descent and the proved `lem:cuts` supply a genuine
Γ-homomorphism-embedding into a tree amalgamation of
full copies of A.

The ordered-pair E-edge rank uses the safe square
budget n*n, so N is a conservative replacement for
the slightly smaller numerical bound in the paper.

This is the fixed-E core of `thm:maintree`. The
additional expansion by a fresh Γ-fixed relation E
and subsequent E-reduct, as well as treatment of
the empty selected substructure, are separate
obligations and are not claimed here.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α β : Type (max u v)}
variable [Finite α] [Finite β]

/-- **Constructive fixed-E restricted coherent EPPA**:
starting with a finite irreducible-structure faithful
coherent EPPA witness for A, there exists a finite
coherent EPPA witness B whose every nonempty closed
substructure of size at most n admits a genuine
homomorphism-embedding into a recursively constructed
tree of full A-copies.

The witness B is the explicit N-fold cycle-sparsening
construction; no additional compactness, unspecified
existence of extensions, or arbitrary tower is used. -/
theorem fixedE_faithfulCoherent_restrictedEPPA
    (act : L.Action Γ)
    (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (B₀ : Structure L β)
    (ψ : Structure.Embedding act A B₀)
    (hCoherent : Structure.IsCoherentEPPAWitness act ψ)
    (hFaithful : Structure.IsIrreducibleStructureFaithful act ψ)
    (n : ℕ) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
        (B : Structure L δ)
        (ι : Structure.Embedding act A B),
      Structure.IsCoherentEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι ∧
      ∀ (S : Set δ) (hS : B.IsClosed S),
        S.Nonempty → S.ncard ≤ n →
          ∃ (W : Type (max u v)) (H : Structure L W),
            TreeAmalgamation act A H ∧
              ∃ f : Structure.Homomorphism act (B.induce S hS) H,
                Structure.Homomorphism.IsHomomorphismEmbedding act f := by
  classical
  obtain ⟨ext⟩ := hCoherent
  have hEPPA : Structure.IsEPPAWitness act ψ :=
    ext.isEPPAWitness
  let s : FaithfulSparseningStage act A :=
    FaithfulSparseningStage.initial act A B₀ ψ hEPPA hFaithful
  let N := n * (n*n+1)
  let t : FaithfulSparseningStage act A :=
    FaithfulSparseningStage.iterate act A E hfix hcomplete s N
  have hCoherentTower :
      Structure.IsCoherentEPPAWitness act t.embedding :=
    FaithfulSparseningStage.iterate_coherent
      act A E hfix hcomplete s ⟨ext⟩ N
  refine ⟨t.Carrier, t.finiteCarrier, t.model,
    t.embedding, hCoherentTower, t.isFaithful, ?_⟩
  intro S hS hNonempty hBound
  let T : ClosedStageSubset act A t :=
    ⟨S, hS⟩
  exact ClosedStageSubset.bounded_tower_homomorphismEmbeds_into_fullATree
    act A E hfix hcomplete s n T hNonempty hBound

end TreeLike
end AllThoseEPPA
