import AllThoseEPPA.CycleSparseningRequiredSwitchComp
import AllThoseEPPA.FaithfulCanonicalPartialAuto

/-!
# Pushing partial automorphisms to the canonical cycle-sparsening copy
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)
variable (E : L.RelSymbol 2)
variable (hfix : act.FixesRel E) (hcomplete : A.EdgeComplete E)

/-- Embed the source of a partial automorphism into the canonical copy. -/
noncomputable def canonicalSourceCopyEmbedding
    (p : Structure.PartialAutomorphism act A) :
    Structure.Embedding act
      (A.induce p.source p.source_closed)
      (witnessStructure B₀ E) :=
  (canonicalEmbedding act A B₀ ψ E hfix hcomplete).comp
    (Structure.inclusion act A p.source p.source_closed)

/-- Embed the source after applying the partial automorphism, again into the
canonical copy. -/
noncomputable def canonicalMovedCopyEmbedding
    (p : Structure.PartialAutomorphism act A) :
    Structure.Embedding act
      (A.induce p.source p.source_closed)
      (witnessStructure B₀ E) :=
  (canonicalEmbedding act A B₀ ψ E hfix hcomplete).comp
    (Faithful.partialAutomorphismSourceEmbedding act p)

/-- The canonical copy of the source of a partial automorphism. -/
def canonicalPartialSourceSet
    (p : Structure.PartialAutomorphism act A) :
    Set (WitnessVertex B₀ E) :=
  Set.range (canonicalSourceCopyEmbedding act A B₀ ψ E hfix hcomplete p)

/-- The canonical source copy is closed. -/
theorem canonicalPartialSourceSet_isClosed
    (p : Structure.PartialAutomorphism act A) :
    (witnessStructure B₀ E).IsClosed
      (canonicalPartialSourceSet act A B₀ ψ E hfix hcomplete p) := by
  exact
    Faithful.embedding_range_isClosed act
      (A.induce p.source p.source_closed)
      (witnessStructure B₀ E)
      (canonicalSourceCopyEmbedding act A B₀ ψ E hfix hcomplete p)

/-- The embedding of the canonical source copy which implements the partial
automorphism. -/
noncomputable def canonicalPartialMoveEmbedding
    (p : Structure.PartialAutomorphism act A) :
    Structure.Embedding act
      ((witnessStructure B₀ E).induce
        (canonicalPartialSourceSet act A B₀ ψ E hfix hcomplete p)
        (canonicalPartialSourceSet_isClosed
          act A B₀ ψ E hfix hcomplete p))
      (witnessStructure B₀ E) := by
  let sourceEmb :=
    canonicalSourceCopyEmbedding act A B₀ ψ E hfix hcomplete p
  let back :=
    Faithful.embeddingInverseOnClosedSubset act sourceEmb
      (canonicalPartialSourceSet act A B₀ ψ E hfix hcomplete p)
      (canonicalPartialSourceSet_isClosed act A B₀ ψ E hfix hcomplete p)
      (by
        intro x hx
        exact hx)
  exact
    (canonicalMovedCopyEmbedding act A B₀ ψ E hfix hcomplete p).comp back

/-- Push a partial automorphism of `A` to the canonical copy inside the
cycle-sparsening witness. -/
noncomputable def canonicalPartialAutomorphism
    (p : Structure.PartialAutomorphism act A) :
    Structure.PartialAutomorphism act
      (witnessStructure B₀ E) :=
  Faithful.partialAutomorphismOfInducedEmbedding
    act (witnessStructure B₀ E)
    (canonicalPartialSourceSet act A B₀ ψ E hfix hcomplete p)
    (canonicalPartialSourceSet_isClosed act A B₀ ψ E hfix hcomplete p)
    (canonicalPartialMoveEmbedding act A B₀ ψ E hfix hcomplete p)

/-- A source vertex of the original partial automorphism belongs to the
canonical source set. -/
theorem canonicalVertex_mem_partialSource
    (p : Structure.PartialAutomorphism act A)
    (a : α) (ha : a ∈ p.source) :
    canonicalVertex act A B₀ ψ E hfix hcomplete a ∈
      canonicalPartialSourceSet act A B₀ ψ E hfix hcomplete p := by
  refine ⟨⟨a, ha⟩, ?_⟩
  rfl

/-- The pushed partial automorphism acts on canonical vertices exactly as the
original partial automorphism acts on `A`. -/
theorem canonicalPartialAutomorphism_apply
    (p : Structure.PartialAutomorphism act A)
    (a : α) (ha : a ∈ p.source) :
    canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete p
        (canonicalVertex act A B₀ ψ E hfix hcomplete a) =
      canonicalVertex act A B₀ ψ E hfix hcomplete (p a) := by
  let sourceEmb :=
    canonicalSourceCopyEmbedding act A B₀ ψ E hfix hcomplete p
  let back :=
    Faithful.embeddingInverseOnClosedSubset act sourceEmb
      (canonicalPartialSourceSet act A B₀ ψ E hfix hcomplete p)
      (canonicalPartialSourceSet_isClosed act A B₀ ψ E hfix hcomplete p)
      (by
        intro x hx
        exact hx)
  let x : canonicalPartialSourceSet act A B₀ ψ E hfix hcomplete p :=
    ⟨canonicalVertex act A B₀ ψ E hfix hcomplete a,
      canonicalVertex_mem_partialSource
        act A B₀ ψ E hfix hcomplete p a ha⟩
  have hbackSpec :=
    Faithful.embeddingInverseOnClosedSubset_apply_spec
      act sourceEmb
      (canonicalPartialSourceSet act A B₀ ψ E hfix hcomplete p)
      (canonicalPartialSourceSet_isClosed act A B₀ ψ E hfix hcomplete p)
      (by
        intro y hy
        exact hy)
      x
  have hsourceA :
      sourceEmb (⟨a, ha⟩ : p.source) =
        canonicalVertex act A B₀ ψ E hfix hcomplete a := by
    rfl
  have hback :
      back x = (⟨a, ha⟩ : p.source) := by
    apply sourceEmb.injective
    exact hbackSpec.trans hsourceA.symm
  have happly :=
    Faithful.partialAutomorphismOfInducedEmbedding_apply
      act (witnessStructure B₀ E)
      (canonicalPartialSourceSet act A B₀ ψ E hfix hcomplete p)
      (canonicalPartialSourceSet_isClosed act A B₀ ψ E hfix hcomplete p)
      (canonicalPartialMoveEmbedding act A B₀ ψ E hfix hcomplete p)
      (canonicalVertex_mem_partialSource
        act A B₀ ψ E hfix hcomplete p a ha)
  have hstep :
      canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete p
          (canonicalVertex act A B₀ ψ E hfix hcomplete a) =
        canonicalPartialMoveEmbedding act A B₀ ψ E hfix hcomplete p x := by
    simpa [canonicalPartialAutomorphism, x] using happly
  rw [hstep]
  change
    canonicalMovedCopyEmbedding act A B₀ ψ E hfix hcomplete p (back x) =
      canonicalVertex act A B₀ ψ E hfix hcomplete (p a)
  rw [hback]
  rfl

/-- The pushed partial automorphism has the expected conjugated language
component. -/
theorem canonicalPartialAutomorphism_lang
    (p : Structure.PartialAutomorphism act A) :
    (canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete p).lang =
      ψ.lang * p.lang * ψ.lang⁻¹ := by
  change
    (ψ.lang * p.lang) * (ψ.lang * 1)⁻¹ =
      ψ.lang * p.lang * ψ.lang⁻¹
  simp

end Sparsening
end AllThoseEPPA
