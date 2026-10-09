import AllThoseEPPA.CycleSparseningClosure

/-!
# Irreducible substructures of the cycle-sparsening witness are generic

This file formalizes Claim `c:cycles:irreducible`.  The argument is the same
free-decomposition argument as for the faithful witness: two nongeneric
internal valuation points determine two proper closed sides, while no
relation tuple can cross both exclusive sides.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w}
variable (act : L.Action Γ)
variable (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

private theorem exclusionSide_closed
    (q : WitnessVertex B₀ E)
    (S : Set (WitnessVertex B₀ E))
    (hS : (witnessStructure B₀ E).IsClosed S) :
    ((witnessStructure B₀ E).induce S hS).IsClosed
      {a : S |
        q ∉ (witnessStructure B₀ E).closureAtSet a.1} := by
  intro n F xs hxs z hz
  let i := UnaryFunctions.unaryIndex F
  have hconst : xs = fun _ => xs i := by
    simpa [i] using
      (UnaryFunctions.unaryTuple_eq_constant F xs)
  have htuple :
      (Subtype.val ∘ xs) = fun _ => (xs i).1 := by
    funext j
    exact congrArg Subtype.val (congrFun hconst j)
  have hzB :
      z.1 ∈
        (witnessStructure B₀ E).func F
          (fun _ => (xs i).1) := by
    change
      z.1 ∈
        (witnessStructure B₀ E).func F
          (Subtype.val ∘ xs) at hz
    rw [htuple] at hz
    exact hz
  have hzcl :
      z.1 ∈
        (witnessStructure B₀ E).closureAtSet (xs i).1 :=
    witness_func_mem_closureAtSet B₀ E F hzB
  change q ∉ (witnessStructure B₀ E).closureAtSet z.1
  intro hqz
  have hq :
      q ∈ (witnessStructure B₀ E).closureAtSet (xs i).1 :=
    (witnessStructure B₀ E).closureAtSet_subset_of_mem
      hzcl hqz
  exact (hxs i) hq

/-- **Claim `c:cycles:irreducible`.** Every irreducible induced
substructure of the cycle-sparsening witness is generic. -/
theorem irreducible_witnessSetGeneric
    (S : Set (WitnessVertex B₀ E))
    (hS : (witnessStructure B₀ E).IsClosed S)
    (hirr :
      ((witnessStructure B₀ E).induce S hS).IsIrreducible) :
    WitnessSetGeneric B₀ E S := by
  classical
  by_contra hgeneric
  unfold WitnessSetGeneric WitnessFamilyGeneric at hgeneric
  push_neg at hgeneric
  rcases hgeneric with ⟨x, y, u, v, hnongeneric⟩

  let left : Set S :=
    {a |
      x.1 ∉ (witnessStructure B₀ E).closureAtSet a.1}
  let right : Set S :=
    {a |
      y.1 ∉ (witnessStructure B₀ E).closureAtSet a.1}

  have hleft_closed :
      ((witnessStructure B₀ E).induce S hS).IsClosed left := by
    exact exclusionSide_closed B₀ E x.1 S hS
  have hright_closed :
      ((witnessStructure B₀ E).induce S hS).IsClosed right := by
    exact exclusionSide_closed B₀ E y.1 S hS

  have hcover : left ∪ right = Set.univ := by
    ext a
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hx :
        x.1 ∈ (witnessStructure B₀ E).closureAtSet a.1
    · right
      change y.1 ∉ (witnessStructure B₀ E).closureAtSet a.1
      intro hy
      have hg :=
        points_generic_of_mem_closure_same_ancestor
          B₀ E a.1 x.1 y.1 hx hy u v
      exact hnongeneric hg
    · left
      exact hx

  have hleft_proper : left ≠ Set.univ := by
    intro h
    have hxleft : x ∈ left := by
      rw [h]
      exact Set.mem_univ x
    exact
      hxleft ((witnessStructure B₀ E).mem_closureAtSet x.1)

  have hright_proper : right ≠ Set.univ := by
    intro h
    have hyright : y ∈ right := by
      rw [h]
      exact Set.mem_univ y
    exact
      hyright ((witnessStructure B₀ E).mem_closureAtSet y.1)

  have hrel_local :
      ∀ {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → S),
        ((witnessStructure B₀ E).induce S hS).rel R xs →
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
        x.1 ∈ (witnessStructure B₀ E).closureAtSet (xs i).1 := by
      by_contra h
      exact hi h
    have hyjclosure :
        y.1 ∈ (witnessStructure B₀ E).closureAtSet (xs j).1 := by
      by_contra h
      exact hj h
    rcases
        pointAt_eq_ancestor_of_mem_closure
          B₀ E (xs i).1 x.1 hxiclosure u with
      ⟨u', hu⟩
    rcases
        pointAt_eq_ancestor_of_mem_closure
          B₀ E (xs j).1 y.1 hyjclosure v with
      ⟨v', hv⟩
    have htupleGeneric :
        WitnessFamilyGeneric B₀ E (fun k => (xs k).1) := by
      exact hrel.2
    have hg := htupleGeneric i j u' v'
    rw [← hu, ← hv] at hg
    exact hnongeneric hg

  have hfunc_cross_empty :
      ∀ {n : ℕ} (F : L.FuncSymbol n) (xs : Fin n → S),
        ¬ ((∀ i, xs i ∈ left) ∨ (∀ i, xs i ∈ right)) →
          ((witnessStructure B₀ E).induce S hS).func F xs = ∅ := by
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
        ((witnessStructure B₀ E).induce S hS) :=
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

/-- Claim `c:cycles:b`, completed: projection from the cycle-sparsening
witness is a homomorphism-embedding. -/
theorem projection_isHomomorphismEmbedding :
    Structure.Homomorphism.IsHomomorphismEmbedding act
      (projection act B₀ E) := by
  intro S hS hirr
  exact
    projection_isEmbeddingOn_of_generic
      act B₀ E S
      (irreducible_witnessSetGeneric
        act B₀ E S hS hirr)

end Sparsening
end AllThoseEPPA
