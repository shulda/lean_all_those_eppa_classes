import AllThoseEPPA.CycleSparseningCanonicalPartialAuto
import AllThoseEPPA.CycleSparseningFaithfulnessEmbedding

/-!
# EPPA for the irreducible-structure sparsening witness

This packages the ordinary-EPPA part of Proposition `prop:faithful`.
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

/-- The canonical copy of the source of a partial automorphism is generic. -/
theorem canonicalPartialSourceSet_generic
    (p : Structure.PartialAutomorphism act A) :
    WitnessSetGeneric B₀ E
      (canonicalPartialSourceSet act A B₀ ψ E hfix hcomplete p) := by
  apply witnessFamilyGeneric_of_pointwise_canonical act A B₀ ψ E hfix hcomplete
  intro i
  rcases i with ⟨x, hx⟩
  rcases hx with ⟨a, hax⟩
  refine ⟨a.1, ?_⟩
  change x = canonicalVertex act A B₀ ψ E hfix hcomplete a.1
  exact hax.symm

/-- The pushed partial automorphism has generic source. -/
theorem canonicalPartialAutomorphism_source_generic
    (p : Structure.PartialAutomorphism act A) :
    WitnessSetGeneric B₀ E
      (canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete p).source := by
  simpa [canonicalPartialAutomorphism] using
    (canonicalPartialSourceSet_generic act A B₀ ψ E hfix hcomplete p)

/-- Every point in the range of the canonical move embedding is canonical. -/
theorem canonicalPartialMoveEmbedding_isCanonical
    (p : Structure.PartialAutomorphism act A)
    (x :
      canonicalPartialSourceSet act A B₀ ψ E hfix hcomplete p) :
    ∃ a : α,
      canonicalPartialMoveEmbedding act A B₀ ψ E hfix hcomplete p x =
        canonicalVertex act A B₀ ψ E hfix hcomplete a := by
  let sourceEmb :=
    canonicalSourceCopyEmbedding act A B₀ ψ E hfix hcomplete p
  let back :=
    Faithful.embeddingInverseOnClosedSubset act sourceEmb
      (canonicalPartialSourceSet act A B₀ ψ E hfix hcomplete p)
      (canonicalPartialSourceSet_isClosed act A B₀ ψ E hfix hcomplete p)
      (by
        intro y hy
        exact hy)
  let y := back x
  refine ⟨p y.1, ?_⟩
  rfl

/-- The pushed partial automorphism has generic target. -/
theorem canonicalPartialAutomorphism_target_generic
    (p : Structure.PartialAutomorphism act A) :
    WitnessSetGeneric B₀ E
      (canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete p).target := by
  have hgen :
      WitnessSetGeneric B₀ E
        (Set.range
          (canonicalPartialMoveEmbedding act A B₀ ψ E hfix hcomplete p)) := by
    apply witnessFamilyGeneric_of_pointwise_canonical act A B₀ ψ E hfix hcomplete
    intro i
    rcases i with ⟨x, hx⟩
    rcases hx with ⟨y, hy⟩
    rcases
        canonicalPartialMoveEmbedding_isCanonical
          act A B₀ ψ E hfix hcomplete p y with
      ⟨a, ha⟩
    exact ⟨a, hy.symm.trans ha⟩
  simpa [canonicalPartialAutomorphism,
    Faithful.inducedEmbeddingRange] using hgen

/-- A base automorphism extending `p` is compatible with the copy of `p`
pushed to the canonical faithful copy. -/
theorem canonicalPartialAutomorphism_baseCompatible
    (p : Structure.PartialAutomorphism act A)
    (g : Structure.Automorphism act B₀)
    (hext : Structure.ExtendsAlong act ψ p g) :
    BaseCompatible act B₀ E
      (canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete p) g := by
  constructor
  · have hlang :=
      congrArg (fun t : Γ => t * ψ.lang⁻¹) hext.1
    rw [canonicalPartialAutomorphism_lang]
    simpa [mul_assoc] using hlang
  · intro x hx
    have hxSource :
        x ∈ canonicalPartialSourceSet act A B₀ ψ E hfix hcomplete p := by
      simpa [canonicalPartialAutomorphism] using hx
    rcases hxSource with ⟨a, hax⟩
    have hxcanon :
        x = canonicalVertex act A B₀ ψ E hfix hcomplete a.1 := by
      exact hax.symm
    rw [hxcanon]
    rw [canonicalPartialAutomorphism_apply
      act A B₀ ψ E hfix hcomplete p a.1 a.2]
    change g (ψ a.1) = ψ (p a.1)
    exact hext.2 a.1 a.2

/-- **Ordinary-EPPA part of Proposition `prop:faithful`.**
If the base witness is an EPPA-witness for `A`, then the sparsening witness is
an EPPA-witness for the canonical copy of `A`. -/
theorem sparseningWitness_isEPPAWitness [Finite β]
    (hB₀ : Structure.IsEPPAWitness act ψ) :
    Structure.IsEPPAWitness act
      (canonicalEmbedding act A B₀ ψ E hfix hcomplete) := by
  intro p
  rcases hB₀ p with ⟨g, hg⟩
  let q :=
    canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete p
  have hsource :
      WitnessSetGeneric B₀ E q.source := by
    simpa [q] using
      (canonicalPartialAutomorphism_source_generic
        act A B₀ ψ E hfix hcomplete p)
  have htarget :
      WitnessSetGeneric B₀ E q.target := by
    simpa [q] using
      (canonicalPartialAutomorphism_target_generic
        act A B₀ ψ E hfix hcomplete p)
  have hcompat :
      BaseCompatible act B₀ E q g := by
    simpa [q] using
      (canonicalPartialAutomorphism_baseCompatible
        act A B₀ ψ E hfix hcomplete p g hg)
  rcases
      sparseningExtension act B₀ E
        q g hfix hcompat hsource htarget with
    ⟨h, hq⟩
  refine ⟨h, ?_⟩
  constructor
  · have hhq : h.lang = q.lang := by
      have hlang := hq.1
      change h.lang * (1 : Γ) = (1 : Γ) * q.lang at hlang
      simpa using hlang
    change h.lang * ψ.lang = ψ.lang * p.lang
    rw [hhq]
    rw [show q.lang =
        ψ.lang * p.lang * ψ.lang⁻¹ by
      simpa [q] using
        (canonicalPartialAutomorphism_lang
          act A B₀ ψ E hfix hcomplete p)]
    simp [mul_assoc]
  · intro a ha
    have hsourceA :
        canonicalVertex act A B₀ ψ E hfix hcomplete a ∈ q.source := by
      simpa [q, canonicalPartialAutomorphism] using
        (canonicalVertex_mem_partialSource
          act A B₀ ψ E hfix hcomplete p a ha)
    have hqa :=
      hq.2 (canonicalVertex act A B₀ ψ E hfix hcomplete a) hsourceA
    change
      h (canonicalVertex act A B₀ ψ E hfix hcomplete a) =
        canonicalVertex act A B₀ ψ E hfix hcomplete (p a)
    calc
      h (canonicalVertex act A B₀ ψ E hfix hcomplete a) =
          q (canonicalVertex act A B₀ ψ E hfix hcomplete a) := by
        simpa [Structure.Embedding.id] using hqa
      _ = canonicalVertex act A B₀ ψ E hfix hcomplete (p a) := by
        simpa [q] using
          (canonicalPartialAutomorphism_apply
            act A B₀ ψ E hfix hcomplete p a ha)

end Sparsening
end AllThoseEPPA
