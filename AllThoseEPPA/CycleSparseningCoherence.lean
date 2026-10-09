import AllThoseEPPA.CycleSparseningEPPA
import AllThoseEPPA.CycleSparseningCanonicalCoherence
import AllThoseEPPA.CycleSparseningLiftCoherence
import AllThoseEPPA.CycleSparseningLiftEquivalent

/-!
# Coherent EPPA for the cycle-sparsening witness

Push partial automorphisms of A into the canonical copy, select their
coherent extensions in the base witness, and apply the source-supported
cycle correction. The XOR cocycle and semidirect product theorems imply
exact composition of the resulting total automorphisms.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w z
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v} {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)
variable (E : L.RelSymbol 2)
variable (hfix : act.FixesRel E) (hcomplete : A.EdgeComplete E)

/-- Canonical lift chosen for the partial automorphism p, using the
chosen coherent base automorphism of p. -/
noncomputable def coherentSparseningLift [Finite β]
    (ext : Structure.CoherentExtension act ψ)
    (p : Structure.PartialAutomorphism act A) :
    Structure.Automorphism act (witnessStructure B₀ E) :=
  sparseningLiftAutomorphism act B₀ E
    (canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete p)
    (ext.extension p) hfix
    (canonicalPartialAutomorphism_baseCompatible
      act A B₀ ψ E hfix hcomplete p (ext.extension p)
      (ext.extension_spec p))

/-- The coherent sparsening lift extends the original partial map along
the canonical embedding of A. -/
theorem coherentSparseningLift_extends [Finite β]
    (ext : Structure.CoherentExtension act ψ)
    (p : Structure.PartialAutomorphism act A) :
    Structure.ExtendsAlong act
      (canonicalEmbedding act A B₀ ψ E hfix hcomplete)
      p (coherentSparseningLift act A B₀ ψ E hfix hcomplete ext p) := by
  let P := canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete p
  let g := ext.extension p
  let hc : BaseCompatible act B₀ E P g :=
    canonicalPartialAutomorphism_baseCompatible
      act A B₀ ψ E hfix hcomplete p g (ext.extension_spec p)
  have hg : Structure.ExtendsAlong act
      (Structure.Embedding.id (witnessStructure B₀ E))
      P (coherentSparseningLift act A B₀ ψ E hfix hcomplete ext p) :=
    sparseningLiftAutomorphism_extends act B₀ E P g hfix hc
      (canonicalPartialAutomorphism_source_generic
        act A B₀ ψ E hfix hcomplete p)
      (canonicalPartialAutomorphism_target_generic
        act A B₀ ψ E hfix hcomplete p)
  constructor
  · change (1 : Γ) * g.lang * ψ.lang = ψ.lang * p.lang
    simpa using (ext.extension_spec p).1
  · intro a ha
    have hsrc : canonicalVertex act A B₀ ψ E hfix hcomplete a ∈ P.source := by
      simpa [P, canonicalPartialAutomorphism] using
        (canonicalVertex_mem_partialSource
          act A B₀ ψ E hfix hcomplete p a ha)
    have hh := hg.2 (canonicalVertex act A B₀ ψ E hfix hcomplete a) hsrc
    change
      coherentSparseningLift act A B₀ ψ E hfix hcomplete ext p
        (canonicalVertex act A B₀ ψ E hfix hcomplete a) =
      canonicalVertex act A B₀ ψ E hfix hcomplete (p a)
    calc
      _ = P (canonicalVertex act A B₀ ψ E hfix hcomplete a) := by
        simpa [Structure.Embedding.id] using hh
      _ = canonicalVertex act A B₀ ψ E hfix hcomplete (p a) :=
        canonicalPartialAutomorphism_apply
          act A B₀ ψ E hfix hcomplete p a ha

/-- Replacing the chosen base automorphism by an equal one does not
change the corrected total sparsening lift. -/
theorem sparseningLiftAutomorphism_eq_of_base_eq [Finite β]
    (P : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g h : Structure.Automorphism act B₀)
    (hgh : g = h)
    (hcG : BaseCompatible act B₀ E P g)
    (hcH : BaseCompatible act B₀ E P h) :
    sparseningLiftAutomorphism act B₀ E P g hfix hcG =
      sparseningLiftAutomorphism act B₀ E P h hfix hcH := by
  subst h
  rfl

/-- Equivalent original partial maps have equal canonical total lifts. -/
theorem coherentSparseningLift_eq_of_equivalent [Finite β]
    (ext : Structure.CoherentExtension act ψ)
    (p q : Structure.PartialAutomorphism act A)
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    coherentSparseningLift act A B₀ ψ E hfix hcomplete ext p =
      coherentSparseningLift act A B₀ ψ E hfix hcomplete ext q := by
  let P := canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete p
  let Q := canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete q
  let gp := ext.extension p
  let gq := ext.extension q
  have heq : gp = gq := ext.respects_equivalent p q hpq
  have hPQ : Structure.PartialIsomorphism.Equivalent P Q :=
    canonicalPartialAutomorphism_equivalent
      act A B₀ ψ E hfix hcomplete p q hpq
  let hcp : BaseCompatible act B₀ E P gp :=
    canonicalPartialAutomorphism_baseCompatible
      act A B₀ ψ E hfix hcomplete p gp (ext.extension_spec p)
  let hcq : BaseCompatible act B₀ E Q gq :=
    canonicalPartialAutomorphism_baseCompatible
      act A B₀ ψ E hfix hcomplete q gq (ext.extension_spec q)
  have hcp' : BaseCompatible act B₀ E P gq := by
    rw [← heq]
    exact hcp
  calc
    coherentSparseningLift act A B₀ ψ E hfix hcomplete ext p =
      sparseningLiftAutomorphism act B₀ E P gp hfix hcp := rfl
    _ = sparseningLiftAutomorphism act B₀ E P gq hfix hcp' :=
      sparseningLiftAutomorphism_eq_of_base_eq
        act B₀ E hfix P gp gq heq hcp hcp'
    _ = sparseningLiftAutomorphism act B₀ E Q gq hfix hcq :=
      sparseningLiftAutomorphism_eq_of_equivalent
        act B₀ E P Q gq hfix hcp' hcq
        (canonicalPartialAutomorphism_source_generic
          act A B₀ ψ E hfix hcomplete p)
        (canonicalPartialAutomorphism_target_generic
          act A B₀ ψ E hfix hcomplete p)
        (canonicalPartialAutomorphism_source_generic
          act A B₀ ψ E hfix hcomplete q)
        (canonicalPartialAutomorphism_target_generic
          act A B₀ ψ E hfix hcomplete q)
        hPQ
    _ = coherentSparseningLift act A B₀ ψ E hfix hcomplete ext q := rfl

/-- Canonically corrected lifts preserve coherent triples exactly. -/
theorem coherentSparseningLift_coherent [Finite β]
    (ext : Structure.CoherentExtension act ψ)
    (p q r : Structure.PartialAutomorphism act A)
    (hcoh : Structure.PartialIsomorphism.CoherentTriple p q r) :
    coherentSparseningLift act A B₀ ψ E hfix hcomplete ext r =
      (coherentSparseningLift act A B₀ ψ E hfix hcomplete ext q).comp
        (coherentSparseningLift act A B₀ ψ E hfix hcomplete ext p) := by
  let P := canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete p
  let Q := canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete q
  let R := canonicalPartialAutomorphism act A B₀ ψ E hfix hcomplete r
  let gp := ext.extension p
  let gq := ext.extension q
  let gr := ext.extension r
  have hbase : gr = gq.comp gp :=
    ext.coherent p q r hcoh
  have hcanon : Structure.PartialIsomorphism.CoherentTriple P Q R :=
    canonicalPartialAutomorphism_coherentTriple
      act A B₀ ψ E hfix hcomplete p q r hcoh
  rcases hcanon with ⟨ht, hReq⟩
  let hcp : BaseCompatible act B₀ E P gp :=
    canonicalPartialAutomorphism_baseCompatible
      act A B₀ ψ E hfix hcomplete p gp (ext.extension_spec p)
  let hcq : BaseCompatible act B₀ E Q gq :=
    canonicalPartialAutomorphism_baseCompatible
      act A B₀ ψ E hfix hcomplete q gq (ext.extension_spec q)
  let hcr : BaseCompatible act B₀ E R gr :=
    canonicalPartialAutomorphism_baseCompatible
      act A B₀ ψ E hfix hcomplete r gr (ext.extension_spec r)
  have hcr' : BaseCompatible act B₀ E R (gq.comp gp) := by
    rw [← hbase]
    exact hcr
  have hcmp : BaseCompatible act B₀ E (Q.comp P ht) (gq.comp gp) :=
    baseCompatible_comp act B₀ E P Q gp gq ht hcp hcq
  have hPsrc : WitnessSetGeneric B₀ E P.source :=
    canonicalPartialAutomorphism_source_generic
      act A B₀ ψ E hfix hcomplete p
  have hPtgt : WitnessSetGeneric B₀ E P.target :=
    canonicalPartialAutomorphism_target_generic
      act A B₀ ψ E hfix hcomplete p
  have hQsrc : WitnessSetGeneric B₀ E Q.source :=
    canonicalPartialAutomorphism_source_generic
      act A B₀ ψ E hfix hcomplete q
  have hQtgt : WitnessSetGeneric B₀ E Q.target :=
    canonicalPartialAutomorphism_target_generic
      act A B₀ ψ E hfix hcomplete q
  have hRsrc : WitnessSetGeneric B₀ E R.source :=
    canonicalPartialAutomorphism_source_generic
      act A B₀ ψ E hfix hcomplete r
  have hRtgt : WitnessSetGeneric B₀ E R.target :=
    canonicalPartialAutomorphism_target_generic
      act A B₀ ψ E hfix hcomplete r
  have hCmpSrc : WitnessSetGeneric B₀ E (Q.comp P ht).source := by
    change WitnessSetGeneric B₀ E P.source
    exact hPsrc
  have hCmpTgt : WitnessSetGeneric B₀ E (Q.comp P ht).target := by
    change WitnessSetGeneric B₀ E Q.target
    exact hQtgt
  calc
    coherentSparseningLift act A B₀ ψ E hfix hcomplete ext r =
      sparseningLiftAutomorphism act B₀ E R gr hfix hcr := rfl
    _ = sparseningLiftAutomorphism act B₀ E R
        (gq.comp gp) hfix hcr' :=
      sparseningLiftAutomorphism_eq_of_base_eq
        act B₀ E hfix R gr (gq.comp gp) hbase hcr hcr'
    _ = sparseningLiftAutomorphism act B₀ E (Q.comp P ht)
        (gq.comp gp) hfix hcmp :=
      sparseningLiftAutomorphism_eq_of_equivalent
        act B₀ E R (Q.comp P ht) (gq.comp gp) hfix
        hcr' hcmp hRsrc hRtgt hCmpSrc hCmpTgt hReq
    _ = (sparseningLiftAutomorphism act B₀ E Q gq hfix hcq).comp
          (sparseningLiftAutomorphism act B₀ E P gp hfix hcp) :=
      sparseningLiftAutomorphism_comp
        act B₀ E P Q gp gq hfix ht hcp hcq hcmp
        hPsrc hPtgt hQsrc hQtgt hCmpSrc hCmpTgt
    _ = (coherentSparseningLift act A B₀ ψ E hfix hcomplete ext q).comp
          (coherentSparseningLift act A B₀ ψ E hfix hcomplete ext p) := rfl

/-- Lift a coherent EPPA selector from B₀ to the sparsening witness. -/
noncomputable def liftSparseningCoherentExtension [Finite β]
    (ext : Structure.CoherentExtension act ψ) :
    Structure.CoherentExtension act
      (canonicalEmbedding act A B₀ ψ E hfix hcomplete) where
  extension := coherentSparseningLift act A B₀ ψ E hfix hcomplete ext
  extension_spec := coherentSparseningLift_extends act A B₀ ψ E hfix hcomplete ext
  respects_equivalent := coherentSparseningLift_eq_of_equivalent act A B₀ ψ E hfix hcomplete ext
  coherent := coherentSparseningLift_coherent act A B₀ ψ E hfix hcomplete ext

/-- Coherent EPPA is preserved by the cycle-sparsening construction. -/
theorem sparseningWitness_isCoherentEPPAWitness [Finite β]
    (hB₀ : Structure.IsCoherentEPPAWitness act ψ) :
    Structure.IsCoherentEPPAWitness act
      (canonicalEmbedding act A B₀ ψ E hfix hcomplete) := by
  rcases hB₀ with ⟨ext⟩
  exact ⟨liftSparseningCoherentExtension
    act A B₀ ψ E hfix hcomplete ext⟩

end Sparsening
end AllThoseEPPA
