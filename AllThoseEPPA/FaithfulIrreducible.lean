import AllThoseEPPA.FaithfulClosure

/-!
# Irreducible substructures of the faithful witness are generic

This file formalizes Claim `c:faithful:irreducible`.  The closure calculus
from `FaithfulClosure` makes the proof close to the paper argument: two
non-generic valuation points determine two proper closed sides, and relation
tuples cannot cross both exclusive sides.
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)

private theorem exclusionSide_closed
    (q : WitnessVertex act A B₀ ψ)
    (S : Set (WitnessVertex act A B₀ ψ))
    (hS : (witnessStructure act A B₀ ψ).IsClosed S) :
    ((witnessStructure act A B₀ ψ).induce S hS).IsClosed
      {a : S |
        q ∉
          (witnessStructure act A B₀ ψ).closureAtSet a.1} := by
  intro n F xs hxs z hz
  let i := UnaryFunctions.unaryIndex F
  have hconst : xs = fun _ => xs i := by
    simpa [i] using
      (UnaryFunctions.unaryTuple_eq_constant F xs)
  have hzB :
      z.1 ∈
        (witnessStructure act A B₀ ψ).func F
          (fun _ => (xs i).1) := by
    change
      z.1 ∈
        (witnessStructure act A B₀ ψ).func F
          (Subtype.val ∘ xs) at hz
    simpa [hconst, Function.comp_def] using hz
  have hzcl :
      z.1 ∈
        (witnessStructure act A B₀ ψ).closureAtSet (xs i).1 :=
    witness_func_mem_closureAtSet act A B₀ ψ F hzB
  change
    q ∉
      (witnessStructure act A B₀ ψ).closureAtSet z.1
  intro hqz
  have hq :
      q ∈
        (witnessStructure act A B₀ ψ).closureAtSet (xs i).1 :=
    (witnessStructure act A B₀ ψ).closureAtSet_subset_of_mem
      hzcl hqz
  exact (hxs i) hq

/-- **Claim `c:faithful:irreducible`.** Every irreducible induced
substructure of the faithful witness is generic. -/
theorem irreducible_witnessSetGeneric
    (S : Set (WitnessVertex act A B₀ ψ))
    (hS : (witnessStructure act A B₀ ψ).IsClosed S)
    (hirr :
      ((witnessStructure act A B₀ ψ).induce S hS).IsIrreducible) :
    WitnessSetGeneric act A B₀ ψ S := by
  classical
  by_contra hgeneric
  unfold WitnessSetGeneric WitnessFamilyGeneric at hgeneric
  push_neg at hgeneric
  rcases hgeneric with ⟨x, y, u, v, hnongeneric⟩

  let left : Set S :=
    {a |
      x.1 ∉
        (witnessStructure act A B₀ ψ).closureAtSet a.1}
  let right : Set S :=
    {a |
      y.1 ∉
        (witnessStructure act A B₀ ψ).closureAtSet a.1}

  have hleft_closed :
      ((witnessStructure act A B₀ ψ).induce S hS).IsClosed left := by
    exact exclusionSide_closed act A B₀ ψ x.1 S hS
  have hright_closed :
      ((witnessStructure act A B₀ ψ).induce S hS).IsClosed right := by
    exact exclusionSide_closed act A B₀ ψ y.1 S hS

  have hcover : left ∪ right = Set.univ := by
    ext a
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hx :
        x.1 ∈
          (witnessStructure act A B₀ ψ).closureAtSet a.1
    · right
      change
        y.1 ∉
          (witnessStructure act A B₀ ψ).closureAtSet a.1
      intro hy
      have hg :=
        points_generic_of_mem_closure_same_ancestor
          act A B₀ ψ a.1 x.1 y.1 hx hy u v
      exact hnongeneric hg
    · left
      exact hx

  have hleft_proper : left ≠ Set.univ := by
    intro h
    have hxleft : x ∈ left := by
      rw [h]
      exact Set.mem_univ x
    exact
      hxleft
        ((witnessStructure act A B₀ ψ).mem_closureAtSet x.1)

  have hright_proper : right ≠ Set.univ := by
    intro h
    have hyright : y ∈ right := by
      rw [h]
      exact Set.mem_univ y
    exact
      hyright
        ((witnessStructure act A B₀ ψ).mem_closureAtSet y.1)

  have hrel_local :
      ∀ {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → S),
        ((witnessStructure act A B₀ ψ).induce S hS).rel R xs →
          (∀ i, xs i ∈ left) ∨ (∀ i, xs i ∈ right) := by
    intro n R xs hrel
    by_cases hL : ∀ i, xs i ∈ left
    · exact Or.inl hL
    by_cases hR : ∀ i, xs i ∈ right
    · exact Or.inr hR
    exfalso
    push_neg at hL hR
    rcases hL with ⟨i, hi⟩
    rcases hR with ⟨j, hj⟩
    have hxiclosure :
        x.1 ∈
          (witnessStructure act A B₀ ψ).closureAtSet (xs i).1 := by
      by_contra h
      exact hi h
    have hyjclosure :
        y.1 ∈
          (witnessStructure act A B₀ ψ).closureAtSet (xs j).1 := by
      by_contra h
      exact hj h
    rcases
        pointAt_eq_ancestor_of_mem_closure
          act A B₀ ψ (xs i).1 x.1 hxiclosure u with
      ⟨u', hu⟩
    rcases
        pointAt_eq_ancestor_of_mem_closure
          act A B₀ ψ (xs j).1 y.1 hyjclosure v with
      ⟨v', hv⟩
    have htupleGeneric :
        WitnessFamilyGeneric act A B₀ ψ
          (fun k => (xs k).1) := by
      exact hrel.2
    have hg := htupleGeneric i j u' v'
    rw [← hu, ← hv] at hg
    exact hnongeneric hg

  have hfunc_cross_empty :
      ∀ {n : ℕ} (F : L.FuncSymbol n) (xs : Fin n → S),
        ¬ ((∀ i, xs i ∈ left) ∨ (∀ i, xs i ∈ right)) →
          ((witnessStructure act A B₀ ψ).induce S hS).func F xs =
            ∅ := by
    intro n F xs hcross
    exfalso
    apply hcross
    let i := UnaryFunctions.unaryIndex F
    have hconst : xs = fun _ => xs i := by
      simpa [i] using
        (UnaryFunctions.unaryTuple_eq_constant F xs)
    have hmem : xs i ∈ left ∪ right := by
      rw [hcover]
      exact Set.mem_univ _
    rcases hmem with hli | hri
    · left
      intro j
      rw [hconst]
      exact hli
    · right
      intro j
      rw [hconst]
      exact hri

  let d :
      Structure.FreeDecomposition
        ((witnessStructure act A B₀ ψ).induce S hS) :=
    { left := left
      right := right
      left_closed := hleft_closed
      right_closed := hright_closed
      cover := hcover
      left_proper := hleft_proper
      right_proper := hright_proper
      rel_local := hrel_local
      func_cross_empty := hfunc_cross_empty }

  exact hirr.false d

/-- The faithful projection is consequently a homomorphism-embedding. -/
theorem projection_isHomomorphismEmbedding :
    Structure.Homomorphism.IsHomomorphismEmbedding act
      (projection act A B₀ ψ) := by
  intro S hS hirr
  exact
    projection_isEmbeddingOn_of_generic
      act A B₀ ψ S
      (irreducible_witnessSetGeneric
        act A B₀ ψ S hS hirr)

end Faithful
end AllThoseEPPA
