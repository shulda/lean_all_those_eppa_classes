import AllThoseEPPA.Irreducible

/-!
# Irreducibility is invariant under genuine Γ-isomorphisms

The tree-amalgamation argument repeatedly identifies closed
pieces by exact Γ-structure embeddings, sometimes with nontrivial
permutations of the language. It is therefore important not to
silently replace Γ-isomorphisms with identity-language
equivalences.

This module gives the forward transport theorem directly:
a surjective Γ-embedding transfers irreducibility to its target.
The proof pulls an arbitrary free decomposition of the target
back to the source. Closedness and mixed-function emptiness
use **exact preservation of all set-valued function fibres**;
relation locality uses the language-permutation action.

No unary-arity restriction is used.
-/

namespace AllThoseEPPA
namespace Structure
namespace Embedding

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- A surjective Γ-structure embedding takes an irreducible
structure to an irreducible structure, even for nontrivial
language actions and set-valued function interpretations.

This theorem deliberately requires an *embedding*, not merely
a bijective homomorphism: reflection and exact function
preservation are necessary to transport free amalgamation. -/
theorem irreducible_of_surjective
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Embedding act A B)
    (hSurj : Function.Surjective f.toFun)
    (hIrr : A.IsIrreducible) :
    B.IsIrreducible := by
  constructor
  intro d
  let pull : A.FreeDecomposition :=
    { left := f.toFun ⁻¹' d.left
      right := f.toFun ⁻¹' d.right
      left_closed := by
        intro n F xs hxs y hy
        have hfy :
            f y ∈ B.func (act.onFunc f.lang F) (f.toFun ∘ xs) := by
          rw [← f.map_func F xs]
          exact ⟨y, hy, rfl⟩
        exact d.left_closed (act.onFunc f.lang F)
          (f.toFun ∘ xs) hxs hfy
      right_closed := by
        intro n F xs hxs y hy
        have hfy :
            f y ∈ B.func (act.onFunc f.lang F) (f.toFun ∘ xs) := by
          rw [← f.map_func F xs]
          exact ⟨y, hy, rfl⟩
        exact d.right_closed (act.onFunc f.lang F)
          (f.toFun ∘ xs) hxs hfy
      cover := by
        apply Set.eq_univ_of_forall
        intro x
        have hx : f x ∈ d.left ∪ d.right := by
          rw [d.cover]
          exact Set.mem_univ _
        exact hx
      left_proper := by
        intro hAll
        apply d.left_proper
        apply Set.eq_univ_of_forall
        intro y
        obtain ⟨x, rfl⟩ := hSurj y
        have hx : x ∈ f.toFun ⁻¹' d.left := by
          rw [hAll]
          exact Set.mem_univ _
        exact hx
      right_proper := by
        intro hAll
        apply d.right_proper
        apply Set.eq_univ_of_forall
        intro y
        obtain ⟨x, rfl⟩ := hSurj y
        have hx : x ∈ f.toFun ⁻¹' d.right := by
          rw [hAll]
          exact Set.mem_univ _
        exact hx
      rel_local := by
        intro n R xs hR
        have hRB :
            B.rel (act.onRel f.lang R) (f.toFun ∘ xs) :=
          (f.map_rel_iff R xs).mpr hR
        exact d.rel_local (act.onRel f.lang R)
          (f.toFun ∘ xs) hRB
      func_cross_empty := by
        intro n F xs hCross
        have hCrossB :
            ¬ ((∀ i, (f.toFun ∘ xs) i ∈ d.left) ∨
              (∀ i, (f.toFun ∘ xs) i ∈ d.right)) := by
          intro hSide
          exact hCross hSide
        ext y
        constructor
        · intro hy
          have hfy :
              f y ∈ B.func (act.onFunc f.lang F)
                (f.toFun ∘ xs) := by
            rw [← f.map_func F xs]
            exact ⟨y, hy, rfl⟩
          rw [d.func_cross_empty (act.onFunc f.lang F)
            (f.toFun ∘ xs) hCrossB] at hfy
          exact hfy
        · intro hy
          exact hy.elim }
  exact hIrr.false pull

end Embedding
end Structure
end AllThoseEPPA
