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
  have hAction : action.onRel p.lang RelSymbol.edge = RelSymbol.edge := by
    rw [hpLang]
    exact Language.Action.onRel_one action RelSymbol.edge
  rw [hAction] at h
  simpa [toStructure, Function.comp_apply] using h

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
  have hpne : p x ≠ p y := by
    intro hp
    exact hxy (p.toPartialEquiv.injOn hx hy hp)
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
    (p : GraphPartialAutomorphism G) (x y : α) : Bool := by
  classical
  exact
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
  · have hyx : y ≠ x := Ne.symm hxy
    by_cases hx : x ∈ p.source
    · by_cases hy : y ∈ p.source
      · simp [flipBit, hxy, hyx, hx, hy,
          correctionBit_symm_of_mem G p hxy hx hy]
      · simp [flipBit, hxy, hyx, hx, hy]
    · by_cases hy : y ∈ p.source
      · simp [flipBit, hxy, hyx, hx, hy]
      · simp [flipBit, hxy, hyx, hx, hy]


private theorem xor_cancel_right (a f : Bool) :
    Bool.xor (Bool.xor a f) f = a := by
  cases a <;> cases f <;> rfl

private theorem xor_self_left (a b : Bool) :
    Bool.xor a (Bool.xor a b) = b := by
  cases a <;> cases b <;> rfl

private theorem xor_ne_xor_right_iff (a b f : Bool) :
    (Bool.xor a f ≠ Bool.xor b f) ↔ (a ≠ b) := by
  cases a <;> cases b <;> cases f <;> decide

/-- The action of the graph extension on one witness vertex. -/
noncomputable def extendVertex
    (p : GraphPartialAutomorphism G) (v : WitnessVertex α) :
    WitnessVertex α := by
  classical
  let σ := baseExtension G p
  refine
    { base := σ v.base
      valuation := fun z =>
        Bool.xor (v.valuation (σ.symm z))
          (flipBit G p v.base (σ.symm z))
      self_false := ?_ }
  simp [σ, v.self_false]

@[simp] theorem extendVertex_base
    (p : GraphPartialAutomorphism G) (v : WitnessVertex α) :
    (extendVertex G p v).base = baseExtension G p v.base :=
  rfl

@[simp] theorem extendVertex_valuation_on_baseExtension
    (p : GraphPartialAutomorphism G) (v : WitnessVertex α) (y : α) :
    (extendVertex G p v).valuation (baseExtension G p y) =
      Bool.xor (v.valuation y) (flipBit G p v.base y) := by
  simp [extendVertex]

/-- Explicit inverse to `extendVertex`. -/
noncomputable def unextendVertex
    (p : GraphPartialAutomorphism G) (v : WitnessVertex α) :
    WitnessVertex α := by
  classical
  let σ := baseExtension G p
  refine
    { base := σ.symm v.base
      valuation := fun y =>
        Bool.xor (v.valuation (σ y))
          (flipBit G p (σ.symm v.base) y)
      self_false := ?_ }
  simp [σ, v.self_false]

/-- The vertex map `(x,χ) ↦ (hatφ(x), f_x(χ))` is a permutation of the
witness vertices. -/
noncomputable def vertexExtensionEquiv
    (p : GraphPartialAutomorphism G) :
    WitnessVertex α ≃ WitnessVertex α where
  toFun := extendVertex G p
  invFun := unextendVertex G p
  left_inv := by
    intro v
    apply WitnessVertex.ext
    · simp [extendVertex, unextendVertex]
    · funext y
      simp [extendVertex, unextendVertex, xor_cancel_right]
  right_inv := by
    intro v
    apply WitnessVertex.ext
    · simp [extendVertex, unextendVertex]
    · funext z
      simp [extendVertex, unextendVertex, xor_cancel_right]

@[simp] theorem vertexExtensionEquiv_apply
    (p : GraphPartialAutomorphism G) (v : WitnessVertex α) :
    vertexExtensionEquiv G p v = extendVertex G p v :=
  rfl

/-- Flipping the same unordered pair at both ends preserves the witness
adjacency relation. -/
theorem extendVertex_adj_iff
    (p : GraphPartialAutomorphism G) (v w : WitnessVertex α) :
    (WitnessVertex.witnessGraph α).Adj
        (extendVertex G p v) (extendVertex G p w) ↔
      (WitnessVertex.witnessGraph α).Adj v w := by
  classical
  rw [WitnessVertex.witnessGraph_adj, WitnessVertex.witnessGraph_adj]
  have hflip := flipBit_symm G p w.base v.base
  simp [extendVertex, hflip, xor_ne_xor_right_iff]

/-- On a vertex of the generic copy belonging to the source of `p`, the
witness permutation agrees with `p`. -/
theorem extendVertex_genericVertex_of_mem
    (p : GraphPartialAutomorphism G) {x : α} (hx : x ∈ p.source) :
    extendVertex G p (genericVertex G x) = genericVertex G (p x) := by
  classical
  apply WitnessVertex.ext
  · exact baseExtension_apply_of_mem G p hx
  · funext z
    obtain ⟨y, rfl⟩ := (baseExtension G p).surjective z
    rw [extendVertex_valuation_on_baseExtension]
    by_cases hxy : x = y
    · subst y
      simp [genericVertex, baseExtension_apply_of_mem G p hx]
    · simp [genericVertex, flipBit, hxy, hx, correctionBit,
        xor_self_left]


/-- The witness-vertex permutation as an automorphism in the common
`Γ_L`-structure API. -/
noncomputable def witnessAutomorphism
    (p : GraphPartialAutomorphism G) :
    Structure.Automorphism action
      (toStructure (WitnessVertex.witnessGraph α)) where
  toPartialIsomorphism :=
    { lang := 1
      toPartialEquiv := (vertexExtensionEquiv G p).toPartialEquiv
      source_closed :=
        Structure.isClosed_univ
          (toStructure (WitnessVertex.witnessGraph α))
      target_closed :=
        Structure.isClosed_univ
          (toStructure (WitnessVertex.witnessGraph α))
      map_rel_iff := by
        intro n R x hx
        rw [Language.Action.onRel_one action R]
        cases R with
        | edge =>
          simpa [toStructure, Function.comp_apply] using
            (extendVertex_adj_iff G p (x 0) (x 1))
      map_func := by
        intro n F x hx
        exact Empty.elim F }
  source_eq_univ := rfl
  target_eq_univ := rfl

/-- The constructed witness automorphism extends the given partial
automorphism along the generic embedding. -/
theorem witnessAutomorphism_extends
    (p : GraphPartialAutomorphism G) :
    Structure.ExtendsAlong action (genericEmbedding G) p
      (witnessAutomorphism G p) := by
  constructor
  · exact Subsingleton.elim _ _
  · intro x hx
    change
      extendVertex G p (genericVertex G x) =
        genericVertex G (p x)
    exact extendVertex_genericVertex_of_mem G p hx

/-- The valuation graph is an EPPA-witness for the generic copy of `G`. -/
theorem graphWitness_isEPPAWitness :
    Structure.IsEPPAWitness action (genericEmbedding G) := by
  intro p
  exact ⟨witnessAutomorphism G p, witnessAutomorphism_extends G p⟩

end ExtensionCore

/-- **Finite graphs have EPPA (explicit valuation witness).**

For an arbitrary finite graph, the graph on valuation vertices from Section 3
contains a copy of the graph and is an EPPA-witness for that copy.  The linear
order used for the generic embedding and for coherent extension of the base
partial permutation is chosen internally and is not part of the statement. -/
theorem finiteGraphsHaveEPPA {α : Type u} [Fintype α]
    (G : SimpleGraph α) :
    ∃ ψ : Structure.Embedding action (toStructure G)
        (toStructure (WitnessVertex.witnessGraph α)),
      Structure.IsEPPAWitness action ψ := by
  classical
  letI : LinearOrder α :=
    LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  exact ⟨genericEmbedding G, graphWitness_isEPPAWitness G⟩


end Graph
end AllThoseEPPA
