import AllThoseEPPA.TreeLikeInducedIrreducibles

/-!
# Heredity of embedding every irreducible substructure into A

The actual hypothesis of the paper's `lem:cuts` is stronger than
`IrreduciblesAreCliques`: every irreducible substructure of B
embeds into the distinguished finite structure A.

This file proves that the stronger assumption also survives passing
to a closed induced substructure. The core is an explicit embedding
between two levels of induction and a single induction on their
combined carrier, preserving arbitrary set-valued functions
*exactly*, not just by inclusion.

This is required to attach full copies of A to the complete
leaves of the clique-tree decomposition.
-/

namespace AllThoseEPPA

namespace Structure

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- An exact structure isomorphism (identity language relabelling)
induces a genuine embedding. The equivalence is expressed without
presupposing an EPPA action; any action may be chosen for the
identity language component of the resulting embedding. -/
noncomputable def embeddingOfEquiv
    (act : L.Action Γ)
    (A : Structure L V) (B : Structure L W)
    (e : V ≃ W)
    (hRel : ∀ {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → V),
      B.rel R (e ∘ xs) ↔ A.rel R xs)
    (hFunc : ∀ {n : ℕ} (F : L.FuncSymbol n)
      (xs : Fin n → V) (y : V),
      y ∈ A.func F xs ↔ e y ∈ B.func F (e ∘ xs)) :
    Embedding act A B := by
  refine
    { lang := 1
      toFun := e
      injective := e.injective
      map_rel_iff := ?_
      map_func := ?_ }
  · intro n R xs
    simpa only [act.onRel_one] using hRel R xs
  · intro n F xs
    change imageSet (fun x => e x) (A.func F xs) =
      B.func (act.onFunc (1 : Γ) F) ((fun x => e x) ∘ xs)
    rw [act.onFunc_one]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hFunc F xs x).mp hx
    · intro hy
      obtain ⟨x, rfl⟩ := e.surjective y
      exact ⟨x, (hFunc F xs x).mpr hy, rfl⟩

end Structure

namespace TreeLike

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {α : Type x}

/-- The nested induced structure on S embeds isomorphically into
the ambient B-induced structure on the image of S. -/
noncomputable def nestedInduceEmbedding
    (act : L.Action Γ)
    (B : Structure L V) (T : Set V) (hT : B.IsClosed T)
    (S : Set T) (hS : (B.induce T hT).IsClosed S) :
    Structure.Embedding act
      ((B.induce T hT).induce S hS)
      (B.induce (Subtype.val '' S)
        (Structure.isClosed_image_subtype B T hT S hS)) := by
  let U : Set V := Subtype.val '' S
  let hU : B.IsClosed U :=
    Structure.isClosed_image_subtype B T hT S hS
  let e : S ≃ U := nestedInduceEquiv T S
  exact Structure.embeddingOfEquiv act
    ((B.induce T hT).induce S hS) (B.induce U hU) e
    (by
      intro n R xs
      rfl)
    (by
      intro n F xs y
      rfl)

/-- The stronger local hypothesis in Lemma `lem:cuts`:
every irreducible closed induced substructure of B has a
structure embedding into A. The language component of that
embedding may be any element of Γ. -/
def EveryIrreducibleEmbedsIn
    (act : L.Action Γ) (A : Structure L α)
    (B : Structure L V) : Prop :=
  ∀ (S : Set V) (hS : B.IsClosed S),
    (B.induce S hS).IsIrreducible →
      Nonempty (Structure.Embedding act (B.induce S hS) A)

/-- The full irreducible-substructure embedding hypothesis of
`lem:cuts` is hereditary under passage to a closed substructure.

An irreducible substructure of B|T, induced on S ⊆ T, is
identified by `nestedInduceEmbedding` with the induced structure
of B on the closed image of S. It therefore embeds into A. -/
theorem everyIrreducibleEmbedsIn_induced
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L V)
    (hEvery : EveryIrreducibleEmbedsIn act A B)
    (T : Set V) (hT : B.IsClosed T) :
    EveryIrreducibleEmbedsIn act A (B.induce T hT) := by
  intro S hS hIrr
  let U : Set V := Subtype.val '' S
  let hU : B.IsClosed U :=
    Structure.isClosed_image_subtype B T hT S hS
  have hIrrU : (B.induce U hU).IsIrreducible :=
    nested_induce_irreducible B T hT S hS hIrr
  obtain ⟨f⟩ := hEvery U hU hIrrU
  let e : Structure.Embedding act
      ((B.induce T hT).induce S hS) (B.induce U hU) :=
    nestedInduceEmbedding act B T hT S hS
  exact ⟨f.comp e⟩

end TreeLike
end AllThoseEPPA
