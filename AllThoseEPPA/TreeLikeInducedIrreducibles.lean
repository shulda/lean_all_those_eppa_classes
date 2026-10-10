import AllThoseEPPA.TreeLikeChordalCut
import AllThoseEPPA.TreeLikeInducedCycles

/-!
# Hereditary structural hypotheses for chordal cuts

A recursive tree-amalgamation argument passes from B to a
closed induced substructure. This module supplies the inherited
hypotheses *without* assuming the restricted piece remains a
faithful EPPA witness for the original distinguished copy.

The key step is that irreducibility is invariant under a
bijective, relation- and function-preserving equivalence, and
that nested induced structures are equivalent to induction
on the image of the nested carrier. Hence the condition
`IrreduciblesAreCliques` passes to every closed induced substructure.

Looplessness, symmetry and the absence of bad induced cycles
are inherited as well.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w
variable {L : Language.{u}} {U : Type v} {W : Type w}

/-- Transport irreducibility through a bijection which exactly
preserves the relation and set-valued-function interpretations.
This version does not require an ambient language action. -/
theorem irreducible_of_equiv
    (A : Structure L U) (B : Structure L W)
    (e : U ≃ W)
    (hrel : ∀ {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → U),
      B.rel R (e ∘ xs) ↔ A.rel R xs)
    (hfunc : ∀ {n : ℕ} (F : L.FuncSymbol n)
      (xs : Fin n → U) (y : U),
      y ∈ A.func F xs ↔ e y ∈ B.func F (e ∘ xs))
    (hIrr : A.IsIrreducible) :
    B.IsIrreducible := by
  classical
  constructor
  intro d
  let pulled : A.FreeDecomposition :=
    { left := e ⁻¹' d.left
      right := e ⁻¹' d.right
      left_closed := by
        intro n F xs hxs y hy
        exact d.left_closed F (e ∘ xs) (fun i => hxs i)
          ((hfunc F xs y).mp hy)
      right_closed := by
        intro n F xs hxs y hy
        exact d.right_closed F (e ∘ xs) (fun i => hxs i)
          ((hfunc F xs y).mp hy)
      cover := by
        apply Set.eq_univ_of_forall
        intro x
        have hx : e x ∈ d.left ∪ d.right := by
          rw [d.cover]
          exact Set.mem_univ _
        exact hx
      left_proper := by
        intro hAll
        apply d.left_proper
        apply Set.eq_univ_of_forall
        intro y
        have hx : e.symm y ∈ e ⁻¹' d.left := by
          rw [hAll]
          exact Set.mem_univ _
        change e (e.symm y) ∈ d.left at hx
        simpa using hx
      right_proper := by
        intro hAll
        apply d.right_proper
        apply Set.eq_univ_of_forall
        intro y
        have hx : e.symm y ∈ e ⁻¹' d.right := by
          rw [hAll]
          exact Set.mem_univ _
        change e (e.symm y) ∈ d.right at hx
        simpa using hx
      rel_local := by
        intro n R xs hR
        have hRB : B.rel R (e ∘ xs) := (hrel R xs).mpr hR
        exact d.rel_local R (e ∘ xs) hRB
      func_cross_empty := by
        intro n F xs hcross
        ext y
        constructor
        · intro hy
          have hcrossB :
              ¬ ((∀ i, (e ∘ xs) i ∈ d.left) ∨
                (∀ i, (e ∘ xs) i ∈ d.right)) := by
            intro hSide
            exact hcross hSide
          have hyB : e y ∈ B.func F (e ∘ xs) :=
            (hfunc F xs y).mp hy
          rw [d.func_cross_empty F (e ∘ xs) hcrossB] at hyB
          exact hyB
        · intro hy
          exact hy.elim }
  exact hIrr.false pulled

end Structure

namespace TreeLike

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The two ways of viewing an induced-on-induced carrier are
canonically equivalent. -/
noncomputable def nestedInduceEquiv
    (T : Set V) (S : Set T) :
    S ≃ (Subtype.val '' S : Set V) := by
  classical
  let f : S → (Subtype.val '' S : Set V) :=
    fun x => ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val hxy
  · rintro ⟨y, ⟨t, ht, hty⟩⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    exact hty

/-- Irreducibility of a substructure of an induced structure lifts
to irreducibility of the same closed set in the ambient structure. -/
theorem nested_induce_irreducible
    (B : Structure L V) (T : Set V) (hT : B.IsClosed T)
    (S : Set T) (hS : (B.induce T hT).IsClosed S)
    (hIrr : ((B.induce T hT).induce S hS).IsIrreducible) :
    (B.induce (Subtype.val '' S)
      (Structure.isClosed_image_subtype B T hT S hS)).IsIrreducible := by
  let U : Set V := Subtype.val '' S
  let hU : B.IsClosed U :=
    Structure.isClosed_image_subtype B T hT S hS
  let e : S ≃ U := nestedInduceEquiv T S
  apply Structure.irreducible_of_equiv
    ((B.induce T hT).induce S hS) (B.induce U hU) e
  · intro n R xs
    rfl
  · intro n F xs y
    rfl
  · exact hIrr

/-- The local hypothesis that every irreducible substructure is
an E-clique is hereditary under closed induction. -/
theorem irreduciblesAreCliques_induced
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    (T : Set V) (hT : B.IsClosed T) :
    IrreduciblesAreCliques (B.induce T hT) E := by
  intro S hS hIrr x y hx hy hxy
  let U : Set V := Subtype.val '' S
  let hU : B.IsClosed U :=
    Structure.isClosed_image_subtype B T hT S hS
  have hIrrU : (B.induce U hU).IsIrreducible :=
    nested_induce_irreducible B T hT S hS hIrr
  have hCliq : EdgeClique B E U := hIrred U hU hIrrU
  have hxU : (x : V) ∈ U := ⟨x, hx, rfl⟩
  have hyU : (y : V) ∈ U := ⟨y, hy, rfl⟩
  have hne : (x : V) ≠ (y : V) := by
    intro h
    exact hxy (Subtype.ext h)
  have hEdge : B.Edge E (x : V) (y : V) :=
    hCliq hxU hyU hne
  change B.rel E (Subtype.val ∘ Structure.pairTuple x y)
  rw [Structure.pairTuple_map]
  exact hEdge

/-- The distinguished graph remains loopless in every induced piece. -/
theorem edgeLoopless_induced
    (B : Structure L V) (E : L.RelSymbol 2)
    (hloop : B.EdgeLoopless E)
    (T : Set V) (hT : B.IsClosed T) :
    (B.induce T hT).EdgeLoopless E := by
  intro x h
  change B.rel E (Subtype.val ∘ Structure.pairTuple x x) at h
  rw [Structure.pairTuple_map] at h
  exact hloop x.1 h

/-- The distinguished graph remains symmetric in every induced piece. -/
theorem edgeSymmetric_induced
    (B : Structure L V) (E : L.RelSymbol 2)
    (hsymm : B.EdgeSymmetric E)
    (T : Set V) (hT : B.IsClosed T) :
    (B.induce T hT).EdgeSymmetric E := by
  intro x y
  change
    (B.rel E (Subtype.val ∘ Structure.pairTuple x y) ↔
     B.rel E (Subtype.val ∘ Structure.pairTuple y x))
  rw [Structure.pairTuple_map, Structure.pairTuple_map]
  exact hsymm x.1 y.1

/-- Absence of forbidden induced E-cycles passes to induced pieces. -/
theorem noBadCycles_induced
    (B : Structure L V) (E : L.RelSymbol 2)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False)
    (T : Set V) (hT : B.IsClosed T) :
    ∀ c : Structure.BadCycleSequence (B.induce T hT) E, False := by
  intro c
  exact hNo (liftBadCycle B E T hT c)

end TreeLike
end AllThoseEPPA
