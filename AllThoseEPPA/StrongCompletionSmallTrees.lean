import AllThoseEPPA.StrongCompletionTreeAmalgamationClass
import AllThoseEPPA.TreeLikeHomEmbComposition

/-!
# Complete all small closed pieces using Observation 9.4

This step packages the exact input needed by Definition 11.2.
If every small closed substructure of B admits a homomorphism-
embedding into a literal full-A tree, and A belongs to an
amalgamation class K, then every such small substructure has
an ordinary completion in K.

No **strong** completion is asserted at this stage. This is
intentional: the manuscript's Definition 11.2 requires ordinary
small completions, and Proposition 11.3 need not be invoked
in the proof of Theorem 1.6 under this exact definition.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} {Γ : Type w} [Group Γ]

namespace FiniteAmalgamationClass

/-- Completion in a class K: a homomorphism-embedding into a
finite class member, without global injectivity. -/
def HasCompletion
    {act : L.Action Γ}
    (K : FiniteAmalgamationClass act)
    {V : Type v} (B : Structure L V) : Prop :=
  ∃ (W : Type v) (_ : Finite W) (C : Structure L W),
    K.mem C ∧
    ∃ f : Structure.Homomorphism act B C,
      Structure.Homomorphism.IsHomomorphismEmbedding act f

end FiniteAmalgamationClass

/-- Small local tree representations give precisely the ordinary
small-completion clause of locally finite classes.

The two homomorphism-embeddings (small piece → tree and
tree → finite K member) compose exactly, including Γ-language
permutations and set-valued functions. -/
theorem smallClosedTrees_haveCompletions
    (act : L.Action Γ)
    {U : Type v} (A : Structure L U) [Finite U]
    (hA : A.IsIrreducible)
    (K : FiniteAmalgamationClass act)
    (hKA : K.mem A)
    {V : Type v} (B : Structure L V) (n : ℕ)
    (hSmall :
      ∀ (S : Set V) (hS : B.IsClosed S),
        S.ncard ≤ n →
          ∃ (W : Type v) (H : Structure L W),
            TreeAmalgamation act A H ∧
              ∃ f : Structure.Homomorphism act (B.induce S hS) H,
                Structure.Homomorphism.IsHomomorphismEmbedding act f) :
    ∀ (S : Set V) (hS : B.IsClosed S),
      S.ncard ≤ n →
        K.HasCompletion (B.induce S hS) := by
  intro S hS hCard
  obtain ⟨W, H, hTree, f, hf⟩ := hSmall S hS hCard
  obtain ⟨Z, hZ, E, hE, g, hg⟩ :=
    TreeAmalgamation.completesInAmalgamationClass
      act A hA K hKA hTree
  exact ⟨Z, hZ, E, hE, g.comp f,
    Structure.Homomorphism.comp_isHomomorphismEmbedding
      act g f hg hf⟩

end TreeLike
end AllThoseEPPA
