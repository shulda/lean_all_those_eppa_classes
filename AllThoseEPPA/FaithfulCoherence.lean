import AllThoseEPPA.FaithfulWitnessCoherence
import AllThoseEPPA.FaithfulCanonicalCoherence

/-!
# Coherent EPPA for the irreducible-structure faithful witness
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

/-- The canonical faithful lift of the base extension selected for a partial
automorphism of the original structure. -/
noncomputable def faithfulLiftAutomorphism [Finite β]
    (E : Structure.CoherentExtension act ψ)
    (p : Structure.PartialAutomorphism act A) :
    Structure.Automorphism act
      (witnessStructure act A B₀ ψ) :=
  faithfulWitnessAutomorphism act A B₀ ψ
    (canonicalPartialAutomorphism act A B₀ ψ p)
    (E.extension p)
    (canonicalPartialAutomorphism_source_generic
      act A B₀ ψ p)
    (canonicalPartialAutomorphism_target_generic
      act A B₀ ψ p)
    (canonicalPartialAutomorphism_baseCompatible
      act A B₀ ψ p (E.extension p)
      (E.extension_spec p))

/-- The canonical faithful lift really extends the original partial
automorphism along the canonical embedding. -/
theorem faithfulLiftAutomorphism_extends [Finite β]
    (E : Structure.CoherentExtension act ψ)
    (p : Structure.PartialAutomorphism act A) :
    Structure.ExtendsAlong act
      (canonicalEmbedding act A B₀ ψ)
      p
      (faithfulLiftAutomorphism act A B₀ ψ E p) := by
  constructor
  · change (E.extension p).lang * ψ.lang =
      ψ.lang * p.lang
    exact (E.extension_spec p).1
  · intro a ha
    let P :=
      canonicalPartialAutomorphism act A B₀ ψ p
    have hsrc :
        canonicalVertex act A B₀ ψ a ∈ P.source := by
      simpa [P, canonicalPartialAutomorphism] using
        (canonicalVertex_mem_partialSource
          act A B₀ ψ p a ha)
    change
      WitnessVertex.transport act A B₀ ψ
          P (E.extension p)
          (canonicalPartialAutomorphism_source_generic
            act A B₀ ψ p)
          (canonicalPartialAutomorphism_target_generic
            act A B₀ ψ p)
          (canonicalPartialAutomorphism_baseCompatible
            act A B₀ ψ p (E.extension p)
            (E.extension_spec p))
          (canonicalVertex act A B₀ ψ a) =
        canonicalVertex act A B₀ ψ (p a)
    calc
      WitnessVertex.transport act A B₀ ψ
          P (E.extension p)
          (canonicalPartialAutomorphism_source_generic
            act A B₀ ψ p)
          (canonicalPartialAutomorphism_target_generic
            act A B₀ ψ p)
          (canonicalPartialAutomorphism_baseCompatible
            act A B₀ ψ p (E.extension p)
            (E.extension_spec p))
          (canonicalVertex act A B₀ ψ a) =
        P (canonicalVertex act A B₀ ψ a) := by
          exact
            WitnessVertex.transport_eq_of_mem_source
              act A B₀ ψ P (E.extension p)
              (canonicalPartialAutomorphism_source_generic
                act A B₀ ψ p)
              (canonicalPartialAutomorphism_target_generic
                act A B₀ ψ p)
              (canonicalPartialAutomorphism_baseCompatible
                act A B₀ ψ p (E.extension p)
                (E.extension_spec p))
              (canonicalVertex act A B₀ ψ a) hsrc
      _ = canonicalVertex act A B₀ ψ (p a) := by
        simpa [P] using
          (canonicalPartialAutomorphism_apply
            act A B₀ ψ p a ha)

/-- The canonical faithful lift respects equivalent partial automorphisms. -/
theorem faithfulLiftAutomorphism_eq_of_equivalent [Finite β]
    (E : Structure.CoherentExtension act ψ)
    (p q : Structure.PartialAutomorphism act A)
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    faithfulLiftAutomorphism act A B₀ ψ E p =
      faithfulLiftAutomorphism act A B₀ ψ E q := by
  let P :=
    canonicalPartialAutomorphism act A B₀ ψ p
  let Q :=
    canonicalPartialAutomorphism act A B₀ ψ q
  let gp := E.extension p
  let gq := E.extension q
  have hg : gp = gq := by
    simpa [gp, gq] using E.respects_equivalent p q hpq
  have hPsrc :
      WitnessSetGeneric act A B₀ ψ P.source := by
    simpa [P] using
      (canonicalPartialAutomorphism_source_generic
        act A B₀ ψ p)
  have hPtgt :
      WitnessSetGeneric act A B₀ ψ P.target := by
    simpa [P] using
      (canonicalPartialAutomorphism_target_generic
        act A B₀ ψ p)
  have hQsrc :
      WitnessSetGeneric act A B₀ ψ Q.source := by
    simpa [Q] using
      (canonicalPartialAutomorphism_source_generic
        act A B₀ ψ q)
  have hQtgt :
      WitnessSetGeneric act A B₀ ψ Q.target := by
    simpa [Q] using
      (canonicalPartialAutomorphism_target_generic
        act A B₀ ψ q)
  have hPgp :
      BaseCompatible act A B₀ ψ P gp := by
    simpa [P, gp] using
      (canonicalPartialAutomorphism_baseCompatible
        act A B₀ ψ p (E.extension p)
        (E.extension_spec p))
  have hQgq :
      BaseCompatible act A B₀ ψ Q gq := by
    simpa [Q, gq] using
      (canonicalPartialAutomorphism_baseCompatible
        act A B₀ ψ q (E.extension q)
        (E.extension_spec q))
  have hPgq :
      BaseCompatible act A B₀ ψ P gq := by
    rw [← hg]
    exact hPgp
  have hPQ :
      Structure.PartialIsomorphism.Equivalent P Q := by
    simpa [P, Q] using
      (canonicalPartialAutomorphism_equivalent
        act A B₀ ψ p q hpq)
  apply Structure.Automorphism.ext_of_lang_apply
  · change gp.lang = gq.lang
    exact congrArg Structure.Automorphism.lang hg
  · intro x
    change
      WitnessVertex.transport act A B₀ ψ
          P gp hPsrc hPtgt hPgp x =
        WitnessVertex.transport act A B₀ ψ
          Q gq hQsrc hQtgt hQgq x
    calc
      WitnessVertex.transport act A B₀ ψ
          P gp hPsrc hPtgt hPgp x =
        WitnessVertex.transport act A B₀ ψ
          P gq hPsrc hPtgt hPgq x :=
        WitnessVertex.transport_eq_of_base_eq
          act A B₀ ψ P gp gq hg
          hPsrc hPtgt hPgp hPgq x
      _ =
        WitnessVertex.transport act A B₀ ψ
          Q gq hQsrc hQtgt hQgq x :=
        WitnessVertex.transport_eq_of_equivalent
          act A B₀ ψ P Q gq
          hPsrc hPtgt hQsrc hQtgt
          hPgq hQgq hPQ x

/-- The canonical faithful lift carries coherent triples to exact products of
the selected witness automorphisms. -/
theorem faithfulLiftAutomorphism_coherent [Finite β]
    (E : Structure.CoherentExtension act ψ)
    (p q r : Structure.PartialAutomorphism act A)
    (hcoh : Structure.PartialIsomorphism.CoherentTriple p q r) :
    faithfulLiftAutomorphism act A B₀ ψ E r =
      (faithfulLiftAutomorphism act A B₀ ψ E q).comp
        (faithfulLiftAutomorphism act A B₀ ψ E p) := by
  let P :=
    canonicalPartialAutomorphism act A B₀ ψ p
  let Q :=
    canonicalPartialAutomorphism act A B₀ ψ q
  let R :=
    canonicalPartialAutomorphism act A B₀ ψ r
  let gp := E.extension p
  let gq := E.extension q
  let gr := E.extension r
  have hbase : gr = gq.comp gp := by
    simpa [gp, gq, gr] using E.coherent p q r hcoh
  have hcanon :
      Structure.PartialIsomorphism.CoherentTriple P Q R := by
    simpa [P, Q, R] using
      (canonicalPartialAutomorphism_coherentTriple
        act A B₀ ψ p q r hcoh)
  rcases hcanon with ⟨ht, hReq⟩
  have hPsrc :
      WitnessSetGeneric act A B₀ ψ P.source := by
    simpa [P] using
      (canonicalPartialAutomorphism_source_generic
        act A B₀ ψ p)
  have hPtgt :
      WitnessSetGeneric act A B₀ ψ P.target := by
    simpa [P] using
      (canonicalPartialAutomorphism_target_generic
        act A B₀ ψ p)
  have hQsrc :
      WitnessSetGeneric act A B₀ ψ Q.source := by
    simpa [Q] using
      (canonicalPartialAutomorphism_source_generic
        act A B₀ ψ q)
  have hQtgt :
      WitnessSetGeneric act A B₀ ψ Q.target := by
    simpa [Q] using
      (canonicalPartialAutomorphism_target_generic
        act A B₀ ψ q)
  have hRsrc :
      WitnessSetGeneric act A B₀ ψ R.source := by
    simpa [R] using
      (canonicalPartialAutomorphism_source_generic
        act A B₀ ψ r)
  have hRtgt :
      WitnessSetGeneric act A B₀ ψ R.target := by
    simpa [R] using
      (canonicalPartialAutomorphism_target_generic
        act A B₀ ψ r)
  have hPcompat :
      BaseCompatible act A B₀ ψ P gp := by
    simpa [P, gp] using
      (canonicalPartialAutomorphism_baseCompatible
        act A B₀ ψ p (E.extension p)
        (E.extension_spec p))
  have hQcompat :
      BaseCompatible act A B₀ ψ Q gq := by
    simpa [Q, gq] using
      (canonicalPartialAutomorphism_baseCompatible
        act A B₀ ψ q (E.extension q)
        (E.extension_spec q))
  have hRcompat :
      BaseCompatible act A B₀ ψ R gr := by
    simpa [R, gr] using
      (canonicalPartialAutomorphism_baseCompatible
        act A B₀ ψ r (E.extension r)
        (E.extension_spec r))
  have hRcomp :
      BaseCompatible act A B₀ ψ R (gq.comp gp) := by
    rw [← hbase]
    exact hRcompat
  have hCompSrc :
      WitnessSetGeneric act A B₀ ψ
        (Q.comp P ht).source := by
    change WitnessSetGeneric act A B₀ ψ P.source
    exact hPsrc
  have hCompTgt :
      WitnessSetGeneric act A B₀ ψ
        (Q.comp P ht).target := by
    change WitnessSetGeneric act A B₀ ψ Q.target
    exact hQtgt
  have hCompCompat :
      BaseCompatible act A B₀ ψ
        (Q.comp P ht) (gq.comp gp) :=
    baseCompatible_comp
      act A B₀ ψ P Q gp gq ht
      hPcompat hQcompat
  apply Structure.Automorphism.ext_of_lang_apply
  · change gr.lang = (gq.comp gp).lang
    exact congrArg Structure.Automorphism.lang hbase
  · intro x
    change
      WitnessVertex.transport act A B₀ ψ
          R gr hRsrc hRtgt hRcompat x =
        WitnessVertex.transport act A B₀ ψ
          Q gq hQsrc hQtgt hQcompat
          (WitnessVertex.transport act A B₀ ψ
            P gp hPsrc hPtgt hPcompat x)
    calc
      WitnessVertex.transport act A B₀ ψ
          R gr hRsrc hRtgt hRcompat x =
        WitnessVertex.transport act A B₀ ψ
          R (gq.comp gp) hRsrc hRtgt hRcomp x :=
        WitnessVertex.transport_eq_of_base_eq
          act A B₀ ψ R gr (gq.comp gp) hbase
          hRsrc hRtgt hRcompat hRcomp x
      _ =
        WitnessVertex.transport act A B₀ ψ
          (Q.comp P ht) (gq.comp gp)
          hCompSrc hCompTgt hCompCompat x :=
        WitnessVertex.transport_eq_of_equivalent
          act A B₀ ψ R (Q.comp P ht) (gq.comp gp)
          hRsrc hRtgt hCompSrc hCompTgt
          hRcomp hCompCompat hReq x
      _ =
        WitnessVertex.transport act A B₀ ψ
          Q gq hQsrc hQtgt hQcompat
          (WitnessVertex.transport act A B₀ ψ
            P gp hPsrc hPtgt hPcompat x) :=
        (WitnessVertex.transport_comp
          act A B₀ ψ P Q gp gq ht
          hPsrc hPtgt hQsrc hQtgt
          hPcompat hQcompat
          hCompSrc hCompTgt hCompCompat x).symm

/-- A coherent extension system on the base witness lifts canonically to the
irreducible-structure faithful witness. -/
noncomputable def liftFaithfulCoherentExtension [Finite β]
    (E : Structure.CoherentExtension act ψ) :
    Structure.CoherentExtension act
      (canonicalEmbedding act A B₀ ψ) where
  extension :=
    faithfulLiftAutomorphism act A B₀ ψ E
  extension_spec :=
    faithfulLiftAutomorphism_extends act A B₀ ψ E
  respects_equivalent :=
    faithfulLiftAutomorphism_eq_of_equivalent act A B₀ ψ E
  coherent :=
    faithfulLiftAutomorphism_coherent act A B₀ ψ E

/-- **Coherent-EPPA part of Proposition `prop:faithful`.**  A coherent base
EPPA witness gives a coherent irreducible-structure faithful witness. -/
theorem faithfulWitness_isCoherentEPPAWitness [Finite β]
    (hB₀ : Structure.IsCoherentEPPAWitness act ψ) :
    Structure.IsCoherentEPPAWitness act
      (canonicalEmbedding act A B₀ ψ) := by
  rcases hB₀ with ⟨E⟩
  exact
    ⟨liftFaithfulCoherentExtension
      act A B₀ ψ E⟩


end Faithful
end AllThoseEPPA
