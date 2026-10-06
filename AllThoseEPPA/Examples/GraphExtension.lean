import Mathlib.Data.Fin.VecNotation
import AllThoseEPPA.Examples.GraphWitness
import AllThoseEPPA.FiniteSet

/-!
# Extending partial automorphisms of the generic graph copy

This file formalizes the flipped-pair part of the warm-up graph construction.
-/

namespace AllThoseEPPA
namespace Graph

universe u

section ExtensionCore

variable {α : Type u} [Fintype α] [LinearOrder α]
variable (G : SimpleGraph α)

/-- A partial automorphism of the original graph, expressed in the common
`Γ_L` API.  Via the generic embedding this is the same data as a partial
automorphism of the generic copy inside the witness. -/
abbrev GraphPartialAutomorphism :=
  Structure.PartialAutomorphism action (toStructure G)

/-- A graph partial automorphism preserves adjacency on its domain. -/
theorem partialAutomorphism_adj_iff
    (p : GraphPartialAutomorphism G) {x y : α}
    (hx : x ∈ p.source) (hy : y ∈ p.source) :
    G.Adj (p x) (p y) ↔ G.Adj x y := by
  have htuple :
      ∀ i, (![x, y] : Fin 2 → α) i ∈ p.toPartialEquiv.source := by
    rw [Fin.forall_fin_two]
    exact ⟨hx, hy⟩
  have h := p.map_rel_iff RelSymbol.edge ![x, y] htuple
  have hpLang : p.lang = 1 := Subsingleton.elim _ _
  simpa [toStructure, hpLang, Function.comp_apply] using h

/-- The coherent order-preserving extension of the underlying partial
permutation of base vertices. -/
noncomputable def baseExtension (p : GraphPartialAutomorphism G) :
    Equiv.Perm α :=
  PartialEquiv.orderedExtension p.toPartialEquiv

@[simp] theorem baseExtension_apply_of_mem
    (p : GraphPartialAutomorphism G) {x : α} (hx : x ∈ p.source) :
    baseExtension G p x = p x :=
  PartialEquiv.orderedExtension_apply_of_mem p.toPartialEquiv hx

/-- The correction bit dictated by an endpoint `x` in the domain of `p`.
When `x` lies in the domain, XORing this bit changes the generic valuation
row at `x` into the target generic row at `p x`, after the base
permutation is applied. -/
noncomputable def correctionBit
    (p : GraphPartialAutomorphism G) (x y : α) : Bool :=
  Bool.xor (genericValuation G x y)
    (genericValuation G (p x) (baseExtension G p y))

private theorem xor_cross_of_ne_iff_ne {a b c d : Bool}
    (h : (a ≠ b) ↔ (c ≠ d)) :
    Bool.xor a c = Bool.xor b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- If both endpoints lie in the domain, they prescribe the same correction
bit for their unordered pair.  This is the formal version of the consistency
observation immediately after the definition of the flipped-pair set `F` in
Section 3. -/
theorem correctionBit_symm_of_mem
    (p : GraphPartialAutomorphism G) {x y : α}
    (hxy : x ≠ y) (hx : x ∈ p.source) (hy : y ∈ p.source) :
    correctionBit G p x y = correctionBit G p y x := by
  have hpne : p x ≠ p y :=
    p.toPartialEquiv.injOn hx hy hxy
  have hsource :
      (genericValuation G x y ≠ genericValuation G y x) ↔
        G.Adj x y := by
    have h := witnessGraph_adj_genericVertex_iff G x y
    simpa [WitnessVertex.witnessGraph_adj, genericVertex, hxy] using h
  have htarget :
      (genericValuation G (p x) (p y) ≠
          genericValuation G (p y) (p x)) ↔
        G.Adj (p x) (p y) := by
    have h := witnessGraph_adj_genericVertex_iff G (p x) (p y)
    simpa [WitnessVertex.witnessGraph_adj, genericVertex, hpne] using h
  have hne :
      (genericValuation G x y ≠ genericValuation G y x) ↔
        (genericValuation G (p x) (p y) ≠
          genericValuation G (p y) (p x)) :=
    hsource.trans ((partialAutomorphism_adj_iff G p hx hy).symm.trans htarget.symm)
  unfold correctionBit
  rw [baseExtension_apply_of_mem G p hx,
    baseExtension_apply_of_mem G p hy]
  exact xor_cross_of_ne_iff_ne hne

/-- The symmetric flipped-pair bit `F(x,y)`.

If neither endpoint belongs to the domain there is no flip.  If at least one
does, the first available endpoint determines the correction; the previous
lemma shows that this is independent of the choice when both are available. -/
noncomputable def flipBit
    (p : GraphPartialAutomorphism G) (x y : α) : Bool :=
  if hxy : x = y then false
  else if hx : x ∈ p.source then correctionBit G p x y
  else if hy : y ∈ p.source then correctionBit G p y x
  else false

@[simp] theorem flipBit_self
    (p : GraphPartialAutomorphism G) (x : α) :
    flipBit G p x x = false := by
  simp [flipBit]

theorem flipBit_symm
    (p : GraphPartialAutomorphism G) (x y : α) :
    flipBit G p x y = flipBit G p y x := by
  classical
  by_cases hxy : x = y
  · subst y
    simp
  · have hyx : y ≠ x := hxy.symm
    by_cases hx : x ∈ p.source
    · by_cases hy : y ∈ p.source
      · simp [flipBit, hxy, hyx, hx, hy,
          correctionBit_symm_of_mem G p hxy hx hy]
      · simp [flipBit, hxy, hyx, hx, hy]
    · by_cases hy : y ∈ p.source
      · simp [flipBit, hxy, hyx, hx, hy]
      · simp [flipBit, hxy, hyx, hx, hy]

end ExtensionCore

end Graph
end AllThoseEPPA
