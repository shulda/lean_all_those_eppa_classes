import AllThoseEPPA.TreeLikeFixedERestrictedCoherentEPPA
import AllThoseEPPA.TreeLikeEmptySubstructure

/-!
# Fixed-E restricted coherent EPPA for every small closed substructure

The constructed finite faithful coherent EPPA witness obtained
by iterated sparsening already has the required
homomorphism-embedding of every **nonempty** closed
substructure of size at most n into a tree of full A-copies.

The empty closed substructure must also be treated to match
the actual theorem. It embeds *exactly* back into A, with
inverse Γ-language component of the distinguished embedding
of A into the witness. This remains correct in the presence
of nullary relations: the empty structure's nullary
relation values reflect those of A along that embedding.

Thus **no nonemptiness exception remains** in this fixed-E
version of Theorem thm:maintree. No unrestricted-language
claim is made: adding and subsequently forgetting the
new Γ-fixed complete relation E remains a separate
proof obligation.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α β : Type (max u v)}
variable [Finite α] [Finite β]

/-- A finite faithful coherent EPPA-witness in the fixed-E
language with the **full** restricted small-substructure
property, including the empty closed substructure.

For each closed induced C of B on at most n vertices,
there is a tree amalgamation H of full A-copies and a
homomorphism-embedding C→H. This is the fixed-E core of
the paper's restricted theorem. -/
theorem fixedE_faithfulCoherent_restrictedEPPA_all
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
        S.ncard ≤ n →
          ∃ (W : Type (max u v)) (H : Structure L W),
            TreeAmalgamation act A H ∧
              ∃ f : Structure.Homomorphism act (B.induce S hS) H,
                Structure.Homomorphism.IsHomomorphismEmbedding act f := by
  classical
  obtain ⟨δ, hδ, B, ι, hCoh, hFaith, hSmall⟩ :=
    fixedE_faithfulCoherent_restrictedEPPA
      act A E hfix hcomplete B₀ ψ hCoherent hFaithful n
  refine ⟨δ, hδ, B, ι, hCoh, hFaith, ?_⟩
  intro S hS hBound
  by_cases hNonempty : S.Nonempty
  · exact hSmall S hS hNonempty hBound
  · have hEmpty : S = (∅ : Set δ) := by
      ext x
      constructor
      · intro hx
        exact (hNonempty ⟨x, hx⟩).elim
      · intro hx
        exact hx.elim
    subst S
    obtain ⟨W, H, hTree, ⟨e⟩⟩ :=
      emptyInduced_embedsFullATree act A B ι
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
