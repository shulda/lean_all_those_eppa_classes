import AllThoseEPPA.TreeLikeTowerAncestorHomEmb
import AllThoseEPPA.TreeLikeTowerCycleFreeTree

/-!
# Embed a bounded top substructure homomorphically into a full-A tree

This is the central small-substructure conclusion of the
iterated cycle-sparsening portion of manuscript Theorem
`thm:maintree`:

* the **actual finite tower** has n*(n*n+1) concrete
  sparsening stages;
* bounded rank descent finds a **genuine closed projected
  ancestor** with no long induced E-cycles;
* the Lean-proven `lem:cuts` gives an *exact embedding*
  of that ancestor into a tree of full A-copies;
* a structural induction over its `ProjectedAncestor`
  certificate provides an actual Γ-homomorphism-embedding
  from the original top closed substructure to the ancestor;
* the general composition lemma for Γ-homomorphism-
  embeddings produces the map into the full-A tree.

This is stronger than a mere homomorphism: every closed
irreducible substructure is mapped by an exact embedding,
with relation reflection and equality of all set-valued
function fibres. It is weaker than a globally injective
embedding, as intended by the theorem in the paper.

The further global `thm:maintree` construction must
establish a finite *coherent* EPPA witness from the
appropriate starting witness and then forget the added
E-relation. Those are separate theorem-level obligations.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type (max u v)} [Finite α]

namespace ClosedStageSubset

/-- **Concrete small-substructure tree conclusion.**
For the actual finite sparsening tower and any nonempty closed
subset of its top stage with at most n vertices, there exists
a tree amalgamation of full A-copies and an actual
Γ-homomorphism-embedding of the **original top induced
substructure** into that tree.

The map is the composite of checked induced canonical
projections and the exact embedding supplied by
`lem:cuts` for the chosen cycle-free ancestor.
No abstract tower or arbitrary unconnected maps are used. -/
theorem bounded_tower_homomorphismEmbeds_into_fullATree
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (n : ℕ)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.iterate
        act A E hfix hcomplete s (n*(n*n+1))))
    (hNonempty : T.support.Nonempty)
    (hBound : T.support.ncard ≤ n) :
    ∃ (W : Type (max u v)) (H : Structure L W),
      TreeAmalgamation act A H ∧
        ∃ f : Structure.Homomorphism act
          ((FaithfulSparseningStage.iterate
            act A E hfix hcomplete s (n*(n*n+1))).model.induce
            T.support T.closed) H,
          Structure.Homomorphism.IsHomomorphismEmbedding act f := by
  obtain ⟨j, U, hAncestor, W, H, hTree, ⟨ι⟩⟩ :=
    bounded_tower_has_fullATree_ancestor
      act A E hfix hcomplete s n T hNonempty hBound
  obtain ⟨f, hf⟩ :=
    ProjectedAncestor.exists_homomorphismEmbedding
      act A E hfix hcomplete s hAncestor
  have hι :
      Structure.Homomorphism.IsHomomorphismEmbedding act
        ι.toHomomorphism := by
    intro S hS hIrr
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb hab
      exact ι.injective hab
    · intro m R xs hxs
      exact ι.map_rel_iff R xs
    · intro m F xs hxs
      exact ι.map_func F xs
  exact ⟨W, H, hTree,
    ι.toHomomorphism.comp f,
    Structure.Homomorphism.comp_isHomomorphismEmbedding
      act ι.toHomomorphism f hι hf⟩

end ClosedStageSubset
end TreeLike
