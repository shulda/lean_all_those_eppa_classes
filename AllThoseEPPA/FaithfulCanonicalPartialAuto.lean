import AllThoseEPPA.FaithfulPartialSourceEmbedding

/-!
# Pushing partial automorphisms to the canonical copy in the faithful witness
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

/-- Embed the source of a partial automorphism into the canonical copy. -/
noncomputable def canonicalSourceCopyEmbedding
    (p : Structure.PartialAutomorphism act A) :
    Structure.Embedding act
      (A.induce p.source p.source_closed)
      (witnessStructure act A B₀ ψ) :=
  (canonicalEmbedding act A B₀ ψ).comp
    (Structure.inclusion act A p.source p.source_closed)

/-- Embed the source after applying the partial automorphism, again into the
canonical copy. -/
noncomputable def canonicalMovedCopyEmbedding
    (p : Structure.PartialAutomorphism act A) :
    Structure.Embedding act
      (A.induce p.source p.source_closed)
      (witnessStructure act A B₀ ψ) :=
  (canonicalEmbedding act A B₀ ψ).comp
    (partialAutomorphismSourceEmbedding act p)

/-- The canonical copy of the source of a partial automorphism. -/
def canonicalPartialSourceSet
    (p : Structure.PartialAutomorphism act A) :
    Set (WitnessVertex act A B₀ ψ) :=
  Set.range (canonicalSourceCopyEmbedding act A B₀ ψ p)

/-- The canonical source copy is closed. -/
theorem canonicalPartialSourceSet_isClosed
    (p : Structure.PartialAutomorphism act A) :
    (witnessStructure act A B₀ ψ).IsClosed
      (canonicalPartialSourceSet act A B₀ ψ p) := by
  exact
    embedding_range_isClosed act
      (A.induce p.source p.source_closed)
      (witnessStructure act A B₀ ψ)
      (canonicalSourceCopyEmbedding act A B₀ ψ p)

/-- The embedding of the canonical source copy which implements the partial
automorphism. -/
noncomputable def canonicalPartialMoveEmbedding
    (p : Structure.PartialAutomorphism act A) :
    Structure.Embedding act
      ((witnessStructure act A B₀ ψ).induce
        (canonicalPartialSourceSet act A B₀ ψ p)
        (canonicalPartialSourceSet_isClosed
          act A B₀ ψ p))
      (witnessStructure act A B₀ ψ) := by
  let sourceEmb :=
    canonicalSourceCopyEmbedding act A B₀ ψ p
  let back :=
    embeddingInverseOnClosedSubset act sourceEmb
      (canonicalPartialSourceSet act A B₀ ψ p)
      (canonicalPartialSourceSet_isClosed act A B₀ ψ p)
      (by
        intro x hx
        exact hx)
  exact
    (canonicalMovedCopyEmbedding act A B₀ ψ p).comp back

/-- Push a partial automorphism of `A` to the canonical copy inside the
faithful witness. -/
noncomputable def canonicalPartialAutomorphism
    (p : Structure.PartialAutomorphism act A) :
    Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ) :=
  partialAutomorphismOfInducedEmbedding
    act (witnessStructure act A B₀ ψ)
    (canonicalPartialSourceSet act A B₀ ψ p)
    (canonicalPartialSourceSet_isClosed act A B₀ ψ p)
    (canonicalPartialMoveEmbedding act A B₀ ψ p)

/-- A source vertex of the original partial automorphism belongs to the
canonical source set. -/
theorem canonicalVertex_mem_partialSource
    (p : Structure.PartialAutomorphism act A)
    (a : α) (ha : a ∈ p.source) :
    canonicalVertex act A B₀ ψ a ∈
      canonicalPartialSourceSet act A B₀ ψ p := by
  refine ⟨⟨a, ha⟩, ?_⟩
  rfl

/-- The pushed partial automorphism acts on canonical vertices exactly as the
original partial automorphism acts on `A`. -/
theorem canonicalPartialAutomorphism_apply
    (p : Structure.PartialAutomorphism act A)
    (a : α) (ha : a ∈ p.source) :
    canonicalPartialAutomorphism act A B₀ ψ p
        (canonicalVertex act A B₀ ψ a) =
      canonicalVertex act A B₀ ψ (p a) := by
  let sourceEmb :=
    canonicalSourceCopyEmbedding act A B₀ ψ p
  let sourceSet :=
    canonicalPartialSourceSet act A B₀ ψ p
  let hsourceSet :=
    canonicalPartialSourceSet_isClosed act A B₀ ψ p
  let back :=
    embeddingInverseOnClosedSubset act sourceEmb
      sourceSet hsourceSet
      (by
        intro x hx
        exact hx)
  let x : sourceSet :=
    ⟨canonicalVertex act A B₀ ψ a,
      canonicalVertex_mem_partialSource
        act A B₀ ψ p a ha⟩
  have hbackSpec :=
    embeddingInverseOnClosedSubset_apply_spec
      act sourceEmb sourceSet hsourceSet
      (by
        intro y hy
        exact hy)
      x
  have hsourceA :
      sourceEmb (⟨a, ha⟩ :
        A.induce p.source p.source_closed) =
        canonicalVertex act A B₀ ψ a := by
    rfl
  have hback :
      back x =
        (⟨a, ha⟩ :
          A.induce p.source p.source_closed) := by
    apply sourceEmb.injective
    exact hbackSpec.trans hsourceA.symm
  have happly :=
    partialAutomorphismOfInducedEmbedding_apply
      act (witnessStructure act A B₀ ψ)
      sourceSet hsourceSet
      (canonicalPartialMoveEmbedding act A B₀ ψ p)
      (canonicalVertex_mem_partialSource
        act A B₀ ψ p a ha)
  rw [happly]
  change
    canonicalMovedCopyEmbedding act A B₀ ψ p (back x) =
      canonicalVertex act A B₀ ψ (p a)
  rw [hback]
  rfl

/-- The pushed partial automorphism has the expected conjugated language
component. -/
theorem canonicalPartialAutomorphism_lang
    (p : Structure.PartialAutomorphism act A) :
    (canonicalPartialAutomorphism act A B₀ ψ p).lang =
      ψ.lang * p.lang * ψ.lang⁻¹ := by
  change
    (ψ.lang * p.lang) * (ψ.lang * 1)⁻¹ =
      ψ.lang * p.lang * ψ.lang⁻¹
  simp

end Faithful
end AllThoseEPPA
