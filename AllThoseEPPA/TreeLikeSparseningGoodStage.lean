import AllThoseEPPA.TreeLikeCutsRealization
import AllThoseEPPA.TreeLikeInducedCycles
import AllThoseEPPA.TreeLikeFaithfulEmbeddingBridge
import AllThoseEPPA.CycleSparseningIrreducibleFaithfulness

/-!
# Cycle-free closed subsets of a sparsening witness embed into full A-trees

This is the direct application of the *now Lean-proven* paper
Lemma `lem:cuts` to the first branch of the concrete
cycle-sparsening trichotomy.

Let A embed into a finite irreducible-structure faithful
structure B with a Γ-fixed relation E, complete on A.
The canonical cycle-sparsening witness B' is again
irreducible-structure faithful. Hence every irreducible
closed substructure of B' embeds into A.

If S is a closed subset of B' on which no long induced
E-cycle occurs, the induced structure B'|S is chordal,
and its irreducible closed substructures embed into A.
The already verified `chordal_embedsInFullATree` therefore
provides a **genuine exact Γ-embedding** of B'|S into a
tree amalgamation of full A-copies.

This is the local 'good stage → full A-tree' bridge in
the proof of manuscript `thm:maintree`.

We fix source and witness carriers in the same sufficiently
large universe so that the cycle-valuation witness carrier
and the target A-copy tree also inhabit that universe.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α β : Type (max u v)}

/-- A cycle-free closed subset of the canonical sparsening
witness embeds **exactly** into a tree amalgamation of
full copies of A, using no extra genericity assumptions.

The two required inputs are already independently checked:
irreducible-structure faithfulness survives sparsening, and
the cycle-free alternative for a closed S yields no bad
cycles in its induced structure. -/
theorem sparsening_good_closed_subset_embeds_fullATree
    [Finite α] [Finite β]
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ)
    (S : Set (Sparsening.WitnessVertex B E))
    (hS : (Sparsening.witnessStructure B E).IsClosed S)
    (hNo : ¬ Sparsening.ContainsInducedCycle B E S) :
    ∃ (W : Type (max u v)) (H : Structure L W),
      TreeAmalgamation act A H ∧
        Nonempty (Structure.Embedding act
          ((Sparsening.witnessStructure B E).induce S hS) H) := by
  letI : Finite (Sparsening.WitnessVertex B E) :=
    Sparsening.witnessVertex_finite B E
  have hFaithNew :
      Structure.IsIrreducibleStructureFaithful act
        (Sparsening.canonicalEmbedding
          act A B ψ E hfix hcomplete) :=
    Sparsening.sparseningWitness_isIrreducibleStructureFaithful
      act A B ψ E hfix hcomplete hfaith
  have hEveryNew :
      EveryIrreducibleEmbedsIn act A
        (Sparsening.witnessStructure B E) :=
    everyIrreducibleEmbedsIn_of_faithful
      act A (Sparsening.witnessStructure B E)
      (Sparsening.canonicalEmbedding act A B ψ E hfix hcomplete)
      hFaithNew
  have hEveryInduced :
      EveryIrreducibleEmbedsIn act A
        ((Sparsening.witnessStructure B E).induce S hS) :=
    everyIrreducibleEmbedsIn_induced
      act A (Sparsening.witnessStructure B E) hEveryNew S hS
  have hNoInduced :
      ∀ c : Structure.BadCycleSequence
        ((Sparsening.witnessStructure B E).induce S hS) E, False :=
    sparsening_no_bad_cycle_induced B E S hS hNo
  exact chordal_embedsInFullATree act A
    ((Sparsening.witnessStructure B E).induce S hS)
    E hfix hcomplete hEveryInduced hNoInduced

end TreeLike
end AllThoseEPPA
