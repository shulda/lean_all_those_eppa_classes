import AllThoseEPPA.FaithfulCanonicalPartialAuto

/-!
# EPPA for the irreducible-structure faithful witness

This packages the ordinary-EPPA part of Proposition `prop:faithful`.
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

/-- The canonical copy of the source of a partial automorphism is generic. -/
theorem canonicalPartialSourceSet_generic
    (p : Structure.PartialAutomorphism act A) :
    WitnessSetGeneric act A B₀ ψ
      (canonicalPartialSourceSet act A B₀ ψ p) := by
  apply witnessFamilyGeneric_of_pointwise_canonical act A B₀ ψ
  intro i
  rcases i with ⟨x, hx⟩
  rcases hx with ⟨a, hax⟩
  refine ⟨a.1, ?_⟩
  change x = canonicalVertex act A B₀ ψ a.1
  exact hax.symm

/-- The pushed partial automorphism has generic source. -/
theorem canonicalPartialAutomorphism_source_generic
    (p : Structure.PartialAutomorphism act A) :
    WitnessSetGeneric act A B₀ ψ
      (canonicalPartialAutomorphism act A B₀ ψ p).source := by
  simpa [canonicalPartialAutomorphism] using
    (canonicalPartialSourceSet_generic act A B₀ ψ p)

/-- Every point in the range of the canonical move embedding is canonical. -/
theorem canonicalPartialMoveEmbedding_isCanonical
    (p : Structure.PartialAutomorphism act A)
    (x :
      canonicalPartialSourceSet act A B₀ ψ p) :
    ∃ a : α,
      canonicalPartialMoveEmbedding act A B₀ ψ p x =
        canonicalVertex act A B₀ ψ a := by
  let sourceEmb :
      Structure.Embedding act
        (A.induce p.source p.source_closed)
        (witnessStructure act A B₀ ψ) :=
    canonicalSourceCopyEmbedding act A B₀ ψ p
  let sourceSet : Set (WitnessVertex act A B₀ ψ) :=
    canonicalPartialSourceSet act A B₀ ψ p
  let hsourceSet :
      (witnessStructure act A B₀ ψ).IsClosed sourceSet := by
    simpa [sourceSet] using
      (canonicalPartialSourceSet_isClosed act A B₀ ψ p)
  let back :
      Structure.Embedding act
        ((witnessStructure act A B₀ ψ).induce
          sourceSet hsourceSet)
        (A.induce p.source p.source_closed) :=
    embeddingInverseOnClosedSubset act sourceEmb
      sourceSet hsourceSet
      (by
        intro y hy
        exact hy)
  let y := back x
  refine ⟨p y.1, ?_⟩
  rfl

/-- The pushed partial automorphism has generic target. -/
theorem canonicalPartialAutomorphism_target_generic
    (p : Structure.PartialAutomorphism act A) :
    WitnessSetGeneric act A B₀ ψ
      (canonicalPartialAutomorphism act A B₀ ψ p).target := by
  have hgen :
      WitnessSetGeneric act A B₀ ψ
        (Set.range
          (canonicalPartialMoveEmbedding act A B₀ ψ p)) := by
    apply witnessFamilyGeneric_of_pointwise_canonical act A B₀ ψ
    intro i
    rcases i with ⟨x, hx⟩
    rcases hx with ⟨y, hy⟩
    rcases
        canonicalPartialMoveEmbedding_isCanonical
          act A B₀ ψ p y with
      ⟨a, ha⟩
    exact ⟨a, hy.symm.trans ha⟩
  simpa [canonicalPartialAutomorphism,
    inducedEmbeddingRange] using hgen

/-- A base automorphism extending `p` is compatible with the copy of `p`
pushed to the canonical faithful copy. -/
theorem canonicalPartialAutomorphism_baseCompatible
    (p : Structure.PartialAutomorphism act A)
    (g : Structure.Automorphism act B₀)
    (hext : Structure.ExtendsAlong act ψ p g) :
    BaseCompatible act A B₀ ψ
      (canonicalPartialAutomorphism act A B₀ ψ p) g := by
  constructor
  · have hlang :=
      congrArg (fun t : Γ => t * ψ.lang⁻¹) hext.1
    rw [canonicalPartialAutomorphism_lang]
    simpa [mul_assoc] using hlang
  · intro x hx
    have hxSource :
        x ∈ canonicalPartialSourceSet act A B₀ ψ p := by
      simpa [canonicalPartialAutomorphism] using hx
    rcases hxSource with ⟨a, hax⟩
    have hax' :
        canonicalVertex act A B₀ ψ a.1 = x := by
      exact hax
    subst x
    rw [canonicalPartialAutomorphism_apply
      act A B₀ ψ p a.1 a.2]
    change g (ψ a.1) = ψ (p a.1)
    exact hext.2 a.1 a.2

/-- **Ordinary-EPPA part of Proposition `prop:faithful`.**
If the base witness is an EPPA-witness for `A`, then the faithful witness is
an EPPA-witness for the canonical copy of `A`. -/
theorem faithfulWitness_isEPPAWitness [Finite β]
    (hB₀ : Structure.IsEPPAWitness act ψ) :
    Structure.IsEPPAWitness act
      (canonicalEmbedding act A B₀ ψ) := by
  intro p
  rcases hB₀ p with ⟨g, hg⟩
  let q :=
    canonicalPartialAutomorphism act A B₀ ψ p
  have hsource :
      WitnessSetGeneric act A B₀ ψ q.source := by
    simpa [q] using
      (canonicalPartialAutomorphism_source_generic
        act A B₀ ψ p)
  have htarget :
      WitnessSetGeneric act A B₀ ψ q.target := by
    simpa [q] using
      (canonicalPartialAutomorphism_target_generic
        act A B₀ ψ p)
  have hcompat :
      BaseCompatible act A B₀ ψ q g := by
    simpa [q] using
      (canonicalPartialAutomorphism_baseCompatible
        act A B₀ ψ p g hg)
  rcases
      faithfulExtension act A B₀ ψ
        q g hsource htarget hcompat with
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
          act A B₀ ψ p)]
    simp [mul_assoc]
  · intro a ha
    have hsourceA :
        canonicalVertex act A B₀ ψ a ∈ q.source := by
      simpa [q, canonicalPartialAutomorphism] using
        (canonicalVertex_mem_partialSource
          act A B₀ ψ p a ha)
    have hqa :=
      hq.2 (canonicalVertex act A B₀ ψ a) hsourceA
    change
      h (canonicalVertex act A B₀ ψ a) =
        canonicalVertex act A B₀ ψ (p a)
    calc
      h (canonicalVertex act A B₀ ψ a) =
          q (canonicalVertex act A B₀ ψ a) := by
        simpa [Structure.Embedding.id] using hqa
      _ = canonicalVertex act A B₀ ψ (p a) := by
        simpa [q] using
          (canonicalPartialAutomorphism_apply
            act A B₀ ψ p a ha)

end Faithful
end AllThoseEPPA
