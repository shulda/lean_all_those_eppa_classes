import AllThoseEPPA.UnaryFunctions
import AllThoseEPPA.TreeLikeFullAAmalgamation

/-!
# The empty-substructure edge case in the restricted EPPA theorem

The main finite rank-descent argument treats nonempty closed
induced subsets, since its rank contains a positive-vertex
count hypothesis. The manuscript handles the empty case
separately.

This file formalizes that case without forbidding nullary
relations. If all function symbols are unary, the empty
vertex set is function-closed. Given any exact Γ-embedding
ψ:A↪B, the empty induced substructure of B embeds exactly
into A, with language component ψ.lang⁻¹. Even 0-ary
relation symbols are reflected using ψ.map_rel_iff.

Consequently the empty selected substructure embeds in
the singleton tree amalgamation consisting of A itself.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {α : Type w} {β : Type x}

/-- The empty vertex set is function-closed when every
function symbol has positive (unary) arity. -/
theorem empty_isClosed_unary (B : Structure L β) :
    B.IsClosed (∅ : Set β) := by
  intro n F xs hxs y hy
  exact (hxs (UnaryFunctions.unaryIndex F)).elim

/-- The empty B-induced substructure embeds **exactly** into A.
The inverse Γ-language component also reflects nullary relations. -/
noncomputable def emptyInducedEmbeddingIntoA
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B) :
    Structure.Embedding act
      (B.induce (∅ : Set β) (empty_isClosed_unary B)) A where
  lang := ψ.lang⁻¹
  toFun := fun x => x.2.elim
  injective := by
    intro x y h
    exact x.2.elim
  map_rel_iff := by
    intro n R xs
    let as : Fin n → α := fun i => (xs i).2.elim
    have hR : act.onRel ψ.lang (act.onRel ψ.lang⁻¹ R) = R := by
      rw [← act.onRel_mul]
      simp
    have hMap := ψ.map_rel_iff (act.onRel ψ.lang⁻¹ R) as
    rw [hR] at hMap
    have hTup : ψ.toFun ∘ as = Subtype.val ∘ xs := by
      funext i
      exact (xs i).2.elim
    rw [hTup] at hMap
    change
      A.rel (act.onRel ψ.lang⁻¹ R)
        (fun i => (xs i).2.elim) ↔
      B.rel R (Subtype.val ∘ xs)
    exact hMap.symm
  map_func := by
    intro n F xs
    exact (xs (UnaryFunctions.unaryIndex F)).2.elim

/-- The empty closed substructure embeds in the
single-copy tree amalgamation of full A-copies. -/
theorem emptyInduced_embedsFullATree
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B) :
    ∃ (W : Type w) (H : Structure L W),
      TreeAmalgamation act A H ∧
      Nonempty (Structure.Embedding act
        (B.induce (∅ : Set β) (empty_isClosed_unary B)) H) :=
  ⟨α, A, TreeAmalgamation.singleton act A,
    ⟨emptyInducedEmbeddingIntoA act A B ψ⟩⟩

end TreeLike
end AllThoseEPPA
