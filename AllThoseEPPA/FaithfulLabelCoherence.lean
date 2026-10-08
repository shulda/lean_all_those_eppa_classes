import AllThoseEPPA.FaithfulCanonicalCoherence

/-!
# Coherence of faithful label fibres

This file isolates the composition laws for the partial and total label
bijections used in the faithful witness lift.
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

/-- Used source labels depend only on the source set of the partial
automorphism. -/
theorem usedSourceLabels_eq_of_source_eq
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (I : BadIrreducible act A B₀ ψ)
    (hs : p.source = q.source) :
    usedSourceLabels act A B₀ ψ p I =
      usedSourceLabels act A B₀ ψ q I := by
  ext l
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, ?_, x.2.2⟩, ?_⟩
    · rw [← hs]
      exact x.2.1
    · apply Subtype.ext
      rfl
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, ?_, x.2.2⟩, ?_⟩
    · rw [hs]
      exact x.2.1
    · apply Subtype.ext
      rfl

/-- For a fixed base automorphism, used target labels depend only on the
target set of the partial automorphism. -/
theorem usedTargetLabels_eq_of_target_eq
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (ht : p.target = q.target) :
    usedTargetLabels act A B₀ ψ p g I =
      usedTargetLabels act A B₀ ψ q g I := by
  ext l
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, ?_, x.2.2⟩, ?_⟩
    · rw [← ht]
      exact x.2.1
    · apply Subtype.ext
      rfl
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, ?_, x.2.2⟩, ?_⟩
    · rw [ht]
      exact x.2.1
    · apply Subtype.ext
      rfl

/-- When the target of one faithful partial automorphism is the source of the
next, the intermediate used-label sets agree literally. -/
theorem usedTargetLabels_eq_usedSourceLabels
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (ht : p.target = q.source) :
    usedTargetLabels act A B₀ ψ p g I =
      usedSourceLabels act A B₀ ψ q
        (I.transport act A B₀ ψ g) := by
  ext l
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, ?_, x.2.2⟩, ?_⟩
    · rw [← ht]
      exact x.2.1
    · apply Subtype.ext
      rfl
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, ?_, x.2.2⟩, ?_⟩
    · rw [ht]
      exact x.2.1
    · apply Subtype.ext
      rfl


/-- On a source witness vertex, the partial label equivalence itself sends the
centre label to the centre label of the partial-automorphism image. -/
theorem labelPartialEquiv_centerLabel [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (w : WitnessVertex act A B₀ ψ)
    (hw : w ∈ p.source)
    (hwI : w.base ∈ I.carrier) :
    let htI :
        (p w).base ∈
          (I.transport act A B₀ ψ g).carrier :=
      ⟨w.base, hwI, hcompat.2 w hw⟩
    labelPartialEquiv act A B₀ ψ p g I
        hsource htarget hcompat
        (centerLabel act A B₀ ψ w I hwI) =
      centerLabel act A B₀ ψ (p w)
        (I.transport act A B₀ ψ g) htI := by
  dsimp
  let hused :
      centerLabel act A B₀ ψ w I hwI ∈
        usedSourceLabels act A B₀ ψ p I :=
    ⟨⟨w, hw, hwI⟩, rfl⟩
  rw [show
    labelPartialEquiv act A B₀ ψ p g I
        hsource htarget hcompat
        (centerLabel act A B₀ ψ w I hwI) =
      (usedLabelEquiv act A B₀ ψ p g I
        hsource htarget hcompat
        ⟨centerLabel act A B₀ ψ w I hwI, hused⟩).1 by
    exact
      partialEquivOfSubtypeEquiv_apply_of_mem
        (usedSourceLabels act A B₀ ψ p I)
        (usedTargetLabels act A B₀ ψ p g I)
        (usedLabelEquiv act A B₀ ψ p g I
          hsource htarget hcompat)
        (labelFallbackEquiv act A B₀ ψ g I)
        hused]
  exact
    usedLabelEquiv_centerLabel
      act A B₀ ψ p g I
      hsource htarget hcompat w hw hwI

/-- Compatible base automorphisms compose along composable faithful partial
automorphisms. -/
theorem baseCompatible_comp
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (gp gq : Structure.Automorphism act B₀)
    (ht : p.target = q.source)
    (hp : BaseCompatible act A B₀ ψ p gp)
    (hq : BaseCompatible act A B₀ ψ q gq) :
    BaseCompatible act A B₀ ψ
      (q.comp p ht) (gq.comp gp) := by
  constructor
  · change gq.lang * gp.lang = q.lang * p.lang
    rw [hp.1, hq.1]
  · intro x hx
    have hxp : x ∈ p.source := by
      change x ∈ p.toPartialEquiv.source
      change x ∈
        (p.toPartialEquiv.trans' q.toPartialEquiv ht).source at hx
      simpa [PartialEquiv.trans'] using hx
    have hpxq : p x ∈ q.source := by
      rw [← ht]
      exact p.map_source hxp
    change gq (gp x.base) = (q (p x)).base
    rw [hp.2 x hxp, hq.2 (p x) hpxq]


/-- Equivalent faithful partial automorphisms induce the same mathematical
partial bijection on labels, for a fixed compatible base automorphism. -/
theorem labelPartialEquiv_eqOnSource_of_equivalent [Finite β]
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hsp : WitnessSetGeneric act A B₀ ψ p.source)
    (htp : WitnessSetGeneric act A B₀ ψ p.target)
    (hsq : WitnessSetGeneric act A B₀ ψ q.source)
    (htq : WitnessSetGeneric act A B₀ ψ q.target)
    (hcp : BaseCompatible act A B₀ ψ p g)
    (hcq : BaseCompatible act A B₀ ψ q g)
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    PartialEquiv.EqOnSource
      (labelPartialEquiv act A B₀ ψ p g I hsp htp hcp)
      (labelPartialEquiv act A B₀ ψ q g I hsq htq hcq) := by
  constructor
  · exact
      usedSourceLabels_eq_of_source_eq
        act A B₀ ψ p q I hpq.2.1
  · intro l hl
    change l ∈ usedSourceLabels act A B₀ ψ p I at hl
    rcases hl with ⟨sw, hsw⟩
    rcases sw with ⟨w, hw, hwI⟩
    have hwq : w ∈ q.source := by
      change w ∈ q.toPartialEquiv.source
      change w ∈ p.toPartialEquiv.source at hw
      rw [← hpq.2.1]
      exact hw
    have hpqw : p w = q w :=
      hpq.2.2 hw
    have hpact :=
      labelPartialEquiv_centerLabel
        act A B₀ ψ p g I hsp htp hcp w hw hwI
    have hqact :=
      labelPartialEquiv_centerLabel
        act A B₀ ψ q g I hsq htq hcq w hwq hwI
    rw [← hsw]
    change
      labelPartialEquiv act A B₀ ψ p g I hsp htp hcp
          (centerLabel act A B₀ ψ w I hwI) =
        labelPartialEquiv act A B₀ ψ q g I hsq htq hcq
          (centerLabel act A B₀ ψ w I hwI)
    calc
      labelPartialEquiv act A B₀ ψ p g I hsp htp hcp
          (centerLabel act A B₀ ψ w I hwI) =
        centerLabel act A B₀ ψ (p w)
          (I.transport act A B₀ ψ g)
          ⟨w.base, hwI, hcp.2 w hw⟩ := hpact
      _ =
        centerLabel act A B₀ ψ (q w)
          (I.transport act A B₀ ψ g)
          ⟨w.base, hwI, hcq.2 w hwq⟩ :=
        centerLabel_congr act A B₀ ψ hpqw
          (I.transport act A B₀ ψ g)
          ⟨w.base, hwI, hcp.2 w hw⟩
          ⟨w.base, hwI, hcq.2 w hwq⟩
      _ =
        labelPartialEquiv act A B₀ ψ q g I hsq htq hcq
          (centerLabel act A B₀ ψ w I hwI) := hqact.symm

/-- Consequently, the canonical total label extension is invariant under
equivalent faithful partial automorphisms. -/
theorem labelExtension_eq_of_equivalent [Finite β]
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (hsp : WitnessSetGeneric act A B₀ ψ p.source)
    (htp : WitnessSetGeneric act A B₀ ψ p.target)
    (hsq : WitnessSetGeneric act A B₀ ψ q.source)
    (htq : WitnessSetGeneric act A B₀ ψ q.target)
    (hcp : BaseCompatible act A B₀ ψ p g)
    (hcq : BaseCompatible act A B₀ ψ q g)
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    labelExtension act A B₀ ψ p g I hsp htp hcp =
      labelExtension act A B₀ ψ q g I hsq htq hcq := by
  letI : Fintype (BadLabel act A B₀ ψ I) :=
    badLabelFintype act A B₀ ψ I
  letI :
      Fintype
        (BadLabel act A B₀ ψ
          (I.transport act A B₀ ψ g)) :=
    badLabelFintype act A B₀ ψ
      (I.transport act A B₀ ψ g)
  letI : LinearOrder (BadLabel act A B₀ ψ I) :=
    badLabelLinearOrder act A B₀ ψ I
  letI :
      LinearOrder
        (BadLabel act A B₀ ψ
          (I.transport act A B₀ ψ g)) :=
    badLabelLinearOrder act A B₀ ψ
      (I.transport act A B₀ ψ g)
  let hcard :
      Fintype.card (BadLabel act A B₀ ψ I) =
        Fintype.card
          (BadLabel act A B₀ ψ
            (I.transport act A B₀ ψ g)) := by
    simpa only [Nat.card_eq_fintype_card] using
      (badLabel_transport_card act A B₀ ψ g I)
  change
    PartialEquiv.orderedExtensionOfCardEq
        (labelPartialEquiv act A B₀ ψ p g I hsp htp hcp)
        hcard =
      PartialEquiv.orderedExtensionOfCardEq
        (labelPartialEquiv act A B₀ ψ q g I hsq htq hcq)
        hcard
  exact
    PartialEquiv.orderedExtensionOfCardEq_eq_of_eqOnSource
      hcard
      (labelPartialEquiv_eqOnSource_of_equivalent
        act A B₀ ψ p q g I
        hsp htp hsq htq hcp hcq hpq)


/-- The canonical total label extensions compose once the two target
bad-irreducible indices are identified explicitly.  Abstracting this equality
makes the dependent elimination on label types well-typed. -/
theorem labelExtension_comp_of_transport_eq [Finite β]
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (gp gq : Structure.Automorphism act B₀)
    (ht : p.target = q.source)
    (hsp : WitnessSetGeneric act A B₀ ψ p.source)
    (htp : WitnessSetGeneric act A B₀ ψ p.target)
    (hsq : WitnessSetGeneric act A B₀ ψ q.source)
    (htq : WitnessSetGeneric act A B₀ ψ q.target)
    (hcp : BaseCompatible act A B₀ ψ p gp)
    (hcq : BaseCompatible act A B₀ ψ q gq)
    (hss :
      WitnessSetGeneric act A B₀ ψ (q.comp p ht).source)
    (hst :
      WitnessSetGeneric act A B₀ ψ (q.comp p ht).target)
    (hcs :
      BaseCompatible act A B₀ ψ
        (q.comp p ht) (gq.comp gp))
    (I : BadIrreducible act A B₀ ψ)
    (htransport :
      (I.transport act A B₀ ψ gp).transport
          act A B₀ ψ gq =
        I.transport act A B₀ ψ (gq.comp gp)) :
    (labelExtension act A B₀ ψ p gp I
        hsp htp hcp).trans
      (labelExtension act A B₀ ψ q gq
        (I.transport act A B₀ ψ gp)
        hsq htq hcq) =
    (labelExtension act A B₀ ψ
        (q.comp p ht) (gq.comp gp) I
        hss hst hcs).trans
      (badLabelEquivOfEq act A B₀ ψ htransport.symm) := by
  cases htransport
  simp only [badLabelEquivOfEq, Equiv.trans_refl]
  let J : BadIrreducible act A B₀ ψ :=
    I.transport act A B₀ ψ gp
  let K : BadIrreducible act A B₀ ψ :=
    J.transport act A B₀ ψ gq
  letI : Fintype (BadLabel act A B₀ ψ I) :=
    badLabelFintype act A B₀ ψ I
  letI : Fintype (BadLabel act A B₀ ψ J) :=
    badLabelFintype act A B₀ ψ J
  letI : Fintype (BadLabel act A B₀ ψ K) :=
    badLabelFintype act A B₀ ψ K
  letI : LinearOrder (BadLabel act A B₀ ψ I) :=
    badLabelLinearOrder act A B₀ ψ I
  letI : LinearOrder (BadLabel act A B₀ ψ J) :=
    badLabelLinearOrder act A B₀ ψ J
  letI : LinearOrder (BadLabel act A B₀ ψ K) :=
    badLabelLinearOrder act A B₀ ψ K
  let pp :=
    labelPartialEquiv act A B₀ ψ p gp I hsp htp hcp
  let pq :=
    labelPartialEquiv act A B₀ ψ q gq J hsq htq hcq
  let ps :=
    labelPartialEquiv act A B₀ ψ
      (q.comp p ht) (gq.comp gp) I hss hst hcs
  have hmid : pp.target = pq.source := by
    exact
      usedTargetLabels_eq_usedSourceLabels
        act A B₀ ψ p q gp I ht
  have hscomp : (q.comp p ht).source = p.source := by
    rfl
  have heq :
      PartialEquiv.EqOnSource ps (pp.trans' pq hmid) := by
    constructor
    · change
        usedSourceLabels act A B₀ ψ (q.comp p ht) I =
          usedSourceLabels act A B₀ ψ p I
      exact
        usedSourceLabels_eq_of_source_eq
          act A B₀ ψ (q.comp p ht) p I hscomp
    · intro l hl
      change
        l ∈ usedSourceLabels act A B₀ ψ (q.comp p ht) I at hl
      rcases hl with ⟨sw, hsw⟩
      rcases sw with ⟨w, hws, hwI⟩
      have hwp : w ∈ p.source := by
        rw [← hscomp]
        exact hws
      have hpwq : p w ∈ q.source := by
        rw [← ht]
        exact p.map_source hwp
      let hpwI :
          (p w).base ∈ J.carrier :=
        ⟨w.base, hwI, hcp.2 w hwp⟩
      have hsact :=
        labelPartialEquiv_centerLabel
          act A B₀ ψ
          (q.comp p ht) (gq.comp gp) I
          hss hst hcs w hws hwI
      have hpact :=
        labelPartialEquiv_centerLabel
          act A B₀ ψ p gp I
          hsp htp hcp w hwp hwI
      have hqact :=
        labelPartialEquiv_centerLabel
          act A B₀ ψ q gq J
          hsq htq hcq (p w) hpwq hpwI
      rw [← hsw]
      change
        ps (centerLabel act A B₀ ψ w I hwI) =
          pq (pp (centerLabel act A B₀ ψ w I hwI))
      calc
        ps (centerLabel act A B₀ ψ w I hwI) =
            centerLabel act A B₀ ψ
              ((q.comp p ht) w) K
              ⟨w.base, hwI, hcs.2 w hws⟩ := hsact
        _ =
            centerLabel act A B₀ ψ (q (p w)) K
              ⟨(p w).base, hpwI, hcq.2 (p w) hpwq⟩ := by
          apply centerLabel_congr act A B₀ ψ
          · rfl
          · exact K
          · exact ⟨w.base, hwI, hcs.2 w hws⟩
          · exact
              ⟨(p w).base, hpwI, hcq.2 (p w) hpwq⟩
        _ =
            pq (centerLabel act A B₀ ψ (p w) J hpwI) :=
          hqact.symm
        _ =
            pq (pp (centerLabel act A B₀ ψ w I hwI)) := by
          exact congrArg pq hpact.symm
  have hcardIJ :
      Fintype.card (BadLabel act A B₀ ψ I) =
        Fintype.card (BadLabel act A B₀ ψ J) := by
    simpa only [J, Nat.card_eq_fintype_card] using
      (badLabel_transport_card act A B₀ ψ gp I)
  have hcardJK :
      Fintype.card (BadLabel act A B₀ ψ J) =
        Fintype.card (BadLabel act A B₀ ψ K) := by
    simpa only [K, Nat.card_eq_fintype_card] using
      (badLabel_transport_card act A B₀ ψ gq J)
  have hcardIK :
      Fintype.card (BadLabel act A B₀ ψ I) =
        Fintype.card (BadLabel act A B₀ ψ K) :=
    hcardIJ.trans hcardJK
  change
    (PartialEquiv.orderedExtensionOfCardEq pp hcardIJ).trans
        (PartialEquiv.orderedExtensionOfCardEq pq hcardJK) =
      PartialEquiv.orderedExtensionOfCardEq ps hcardIK
  calc
    (PartialEquiv.orderedExtensionOfCardEq pp hcardIJ).trans
        (PartialEquiv.orderedExtensionOfCardEq pq hcardJK) =
      PartialEquiv.orderedExtensionOfCardEq
        (pp.trans' pq hmid) hcardIK :=
      (PartialEquiv.orderedExtensionOfCardEq_trans'
        pp pq hmid hcardIJ hcardJK hcardIK).symm
    _ =
      PartialEquiv.orderedExtensionOfCardEq ps hcardIK :=
      (PartialEquiv.orderedExtensionOfCardEq_eq_of_eqOnSource
        hcardIK heq).symm

/-- The canonical total label extensions compose for an exact composition of
faithful partial automorphisms and compatible base automorphisms. -/
theorem labelExtension_comp [Finite β]
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (gp gq : Structure.Automorphism act B₀)
    (ht : p.target = q.source)
    (hsp : WitnessSetGeneric act A B₀ ψ p.source)
    (htp : WitnessSetGeneric act A B₀ ψ p.target)
    (hsq : WitnessSetGeneric act A B₀ ψ q.source)
    (htq : WitnessSetGeneric act A B₀ ψ q.target)
    (hcp : BaseCompatible act A B₀ ψ p gp)
    (hcq : BaseCompatible act A B₀ ψ q gq)
    (hss :
      WitnessSetGeneric act A B₀ ψ (q.comp p ht).source)
    (hst :
      WitnessSetGeneric act A B₀ ψ (q.comp p ht).target)
    (hcs :
      BaseCompatible act A B₀ ψ
        (q.comp p ht) (gq.comp gp))
    (I : BadIrreducible act A B₀ ψ) :
    (labelExtension act A B₀ ψ p gp I
        hsp htp hcp).trans
      (labelExtension act A B₀ ψ q gq
        (I.transport act A B₀ ψ gp)
        hsq htq hcq) =
    (labelExtension act A B₀ ψ
        (q.comp p ht) (gq.comp gp) I
        hss hst hcs).trans
      (badLabelEquivOfEq act A B₀ ψ
        (BadIrreducible.transport_comp
          act A B₀ ψ gq gp I).symm) := by
  exact
    labelExtension_comp_of_transport_eq
      act A B₀ ψ p q gp gq ht
      hsp htp hsq htq hcp hcq
      hss hst hcs I
      (BadIrreducible.transport_comp
        act A B₀ ψ gq gp I)

end Faithful
end AllThoseEPPA
