import AllThoseEPPA.TreeLikeInfiniteCopiesTreeInduction
import AllThoseEPPA.TreeLikeCompleteIrreducible
import AllThoseEPPA.TreeLikeFreshBinaryComplete
import AllThoseEPPA.TreeLikeFreshBinaryWitnessReduct
import AllThoseEPPA.TreeLikeFreshBinaryIrreducibility

/-!
# The manuscript infinitecopies lemma for canonical fresh E expansions

Let A be ANY finite Γ-structure in the old unary-function
language, and M any (possibly infinite) Γ-structure containing
a copy of A along which every partial automorphism of A extends.

Add the fresh Γ-fixed binary E as the complete loopless
graph to *both* A and M. The expanded A is irreducible,
even if the original A is not. The full Γ-tree-into-M
induction therefore applies to any literal tree
amalgamation D of full copies of expanded A.

Forgetting E from its Γ-homomorphism-embedding D→M⁺
gives a real Γ-homomorphism-embedding D⁻→M. Every
expanded A-copy α in D can furthermore be moved back
pointwise (and in Γ-language) to the chosen A-copy
inside M by an automorphism of M.

This is stronger than the setwise "moreover" part of the
manuscript's Lemma lem:infinitecopies. The only difference
from its literal input statement is that the complete-E
expansion is written in its canonical explicit form, not
as an isomorphic arbitrary structure with complete E.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {V : Type v} {M : Type x}

/-- Infinitecopies lemma for literal canonical E-expanded
sources: a tree of full A⁺ copies homomorphism-embeds after
forgetting E into any ambient M extending partial
automorphisms of A. Every expanded A⁺ copy can be
normalized to the fixed embedded A, *pointwise* and with
exact Γ-language component. -/
theorem completeFreshETree_realizesIntoAmbient
    (act : L.Action Γ)
    (A : Structure L V) [Finite V]
    (N : Structure L M)
    (a : Structure.Embedding act A N)
    (hExt : Structure.IsEPPAWitness act a)
    {U : Type v}
    (D : Structure L.withFixedBinaryRel U)
    (hTree : TreeAmalgamation act.withFixedBinaryRel
      A.withCompleteFixedBinary D) :
    ∃ h : Structure.Homomorphism act D.forgetFixedBinary N,
      Structure.Homomorphism.IsHomomorphismEmbedding act h ∧
      ∀ β : Structure.Embedding act.withFixedBinaryRel
          A.withCompleteFixedBinary D,
        ∃ σ : Structure.Automorphism act N,
          σ.lang * h.lang * (β.forgetFixedBinary act).lang = a.lang ∧
          ∀ x : V, σ (h (β x)) = a x := by
  classical
  let actPlus : L.withFixedBinaryRel.Action Γ :=
    act.withFixedBinaryRel
  let Aplus : Structure L.withFixedBinaryRel V :=
    A.withCompleteFixedBinary
  let Nplus : Structure L.withFixedBinaryRel M :=
    N.withCompleteFixedBinary
  let aPlus : Structure.Embedding actPlus Aplus Nplus :=
    a.withCompleteFixedBinary act
  have hAplusIrr : Aplus.IsIrreducible :=
    edgeComplete_isIrreducible
      Aplus (Language.withFixedBinaryRel.freshE L)
      (Structure.withCompleteFixedBinary_edgeComplete A)
  have hPlusExt : Structure.IsEPPAWitness actPlus aPlus :=
    Structure.isEPPAWitness_withCompleteFixedBinary act a hExt
  obtain ⟨hPlus, hhPlus, hNormalizePlus⟩ :=
    TreeAmalgamation.realizeIntoAmbient
      actPlus Aplus hAplusIrr Nplus aPlus hPlusExt hTree
  let h : Structure.Homomorphism act D.forgetFixedBinary N :=
    hPlus.forgetFixedBinary act
  have hh : Structure.Homomorphism.IsHomomorphismEmbedding act h :=
    Structure.Homomorphism.forgetFixedBinary_isHomomorphismEmbedding
      act hPlus hhPlus
  refine ⟨h, hh, ?_⟩
  intro β
  obtain ⟨σ, hLang, hApply⟩ := hNormalizePlus β
  let σOld : Structure.Automorphism act N :=
    σ.forgetFixedBinary act
  refine ⟨σOld, ?_, ?_⟩
  · exact hLang
  · intro x
    exact hApply x

end TreeLike
end AllThoseEPPA
