import AllThoseEPPA.CycleSparseningSemidirect

/-!
# Local bit discrepancies for lifting partial automorphisms

This is the Boolean counterpart of the `centerLabel` and
`BaseCompatible` infrastructure from the faithful construction.
It isolates the finite support information used to choose one global
switch for each indexed bad cycle.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Centre point in the one-point closure carried by a witness vertex. -/
def centerPoint (w : WitnessVertex B₀ E) :
    B₀.closureAtSet (w.base B₀ E) :=
  ⟨w.base B₀ E, B₀.mem_closureAtSet (w.base B₀ E)⟩

/-- Centre valuation point, including its entire binary cycle valuation. -/
def centerValuationPoint (w : WitnessVertex B₀ E) :
    ValuationPoint B₀ E :=
  w.pointAt B₀ E (centerPoint B₀ E w)

/-- The bit read from the centre valuation of a witness vertex at a
specified bad cycle containing its base coordinate. -/
def centerBit (w : WitnessVertex B₀ E)
    (c : Structure.BadCycleSequence B₀ E)
    (hwc : w.base B₀ E ∈ c.carrier) : Bool :=
  (centerValuationPoint B₀ E w).2 ⟨c, hwc⟩

/-- The base automorphism agrees with a partial witness automorphism
on the latter's language component and projected source. -/
def BaseCompatible
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀) : Prop :=
  g.lang = p.lang ∧
    ∀ w, w ∈ p.source →
      g (w.base B₀ E) = (p w).base B₀ E

/-- Source vertices of a partial automorphism whose base is on c. -/
abbrev SourceWitness
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (c : Structure.BadCycleSequence B₀ E) :=
  {w : WitnessVertex B₀ E //
    w ∈ p.source ∧ w.base B₀ E ∈ c.carrier}

/-- The Boolean discrepancy of the source and its image on a bad cycle.
Coherence requires choosing this bit consistently across source vertices. -/
def bitDiscrepancy
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g)
    (w : WitnessVertex B₀ E)
    (hw : w ∈ p.source)
    (c : Structure.BadCycleSequence B₀ E)
    (hwc : w.base B₀ E ∈ c.carrier) : Bool :=
  let htarget : (p w).base B₀ E ∈ (c.transport g hfix).carrier := by
    have h :=
      (Structure.BadCycleSequence.mem_transport_carrier_iff
        c g hfix (w.base B₀ E)).2 hwc
    rw [← hcompat.2 w hw]
    exact h
  centerBit B₀ E w c hwc !=
    centerBit B₀ E (p w) (c.transport g hfix) htarget

/-- Centre valuation points of any two vertices from a generic source
of a partial automorphism are themselves generic. -/
theorem centerValuationPoints_generic_of_source
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (hsource : WitnessSetGeneric B₀ E p.source)
    (w z : WitnessVertex B₀ E)
    (hw : w ∈ p.source) (hz : z ∈ p.source) :
    AreGeneric B₀ E (centerValuationPoint B₀ E w)
      (centerValuationPoint B₀ E z) :=
  hsource ⟨w, hw⟩ ⟨z, hz⟩
    (centerPoint B₀ E w) (centerPoint B₀ E z)

/-- A four-bit parity identity: matching source and target equality patterns
give the same source-to-target discrepancy for either chosen endpoint. -/
theorem bool_discrepancy_eq_of_parity
    (a b c d : Bool)
    (h : (a = b) ↔ (c = d)) :
    (a != c) = (b != d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- Compatibility of base automorphisms is closed under composition.
This is the same formal lemma as for the irreducible-faithful construction. -/
theorem baseCompatible_comp
    (p q : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (gp gq : Structure.Automorphism act B₀)
    (ht : p.target = q.source)
    (hp : BaseCompatible act B₀ E p gp)
    (hq : BaseCompatible act B₀ E q gq) :
    BaseCompatible act B₀ E (q.comp p ht) (gq.comp gp) := by
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
    change
      gq (gp (x.base B₀ E)) = (q (p x)).base B₀ E
    rw [hp.2 x hxp, hq.2 (p x) hpxq]

/-- On a bad cycle, the bits of two distinct generic centre points agree
exactly when their vertices form an ordinary (non-closing) cycle edge. -/
theorem generic_centerBits_eq_iff_nonWrap
    (w z : WitnessVertex B₀ E)
    (c : Structure.BadCycleSequence B₀ E)
    (hwc : w.base B₀ E ∈ c.carrier)
    (hzc : z.base B₀ E ∈ c.carrier)
    (hne : w.base B₀ E ≠ z.base B₀ E)
    (hgen : AreGeneric B₀ E
      (centerValuationPoint B₀ E w)
      (centerValuationPoint B₀ E z)) :
    (centerBit B₀ E w c hwc = centerBit B₀ E z c hzc) ↔
      c.NonWrapPair (w.base B₀ E) (z.base B₀ E) := by
  rcases hgen with heq | ⟨_, hcycles⟩
  · exact (hne (congrArg Sigma.fst heq)).elim
  · rcases hcycles c hwc hzc with ⟨hnw, heq⟩ | ⟨hw, hneq⟩
    · exact ⟨fun _ => hnw, fun _ => heq⟩
    · constructor
      · intro heq
        exact (hneq heq).elim
      · intro hnw
        exact ((c.nonWrapPair_not_wrap hnw) hw).elim

end Sparsening
end AllThoseEPPA
