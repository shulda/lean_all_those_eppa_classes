import AllThoseEPPA.CycleSparseningTransportGeneric

/-!
# Reflection of genericity under cycle reindexing

This is the converse to `areGeneric_transport`. It is proved directly
rather than via an equality of dependent transports by g and g.symm.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w}
variable (act : L.Action Γ) (A : Structure L V) (E : L.RelSymbol 2)

/-- Valuations evaluated on an explicitly transported source cycle keep
their Boolean bit. -/
theorem valuationPointTransport_eval_image
    (g : Structure.Automorphism act A)
    (hfix : act.FixesRel E)
    (p : ValuationPoint A E)
    (c : Structure.BadCycleSequence A E)
    (hp : p.1 ∈ c.carrier) :
    (valuationPointTransport act A E g hfix p).2
        ⟨c.transport g hfix,
          (Structure.BadCycleSequence.mem_transport_carrier_iff
            c g hfix p.1).2 hp⟩ =
      p.2 ⟨c, hp⟩ := by
  change
    valuationFunctionTransportEquiv act A E g hfix p.1 p.2
      (badCyclesAtEquiv act A E g hfix p.1 ⟨c, hp⟩) =
    p.2 ⟨c, hp⟩
  exact valuationFunctionTransportEquiv_apply_transport
    act A E g hfix p.1 p.2 ⟨c, hp⟩

/-- If the transported valuation points are generic, so were the originals. -/
theorem areGeneric_of_transport
    (g : Structure.Automorphism act A)
    (hfix : act.FixesRel E)
    {p q : ValuationPoint A E}
    (hgen : AreGeneric A E
      (valuationPointTransport act A E g hfix p)
      (valuationPointTransport act A E g hfix q)) :
    AreGeneric A E p q := by
  rcases hgen with heq | ⟨hne, hcycles⟩
  · exact Or.inl
      (valuationPointTransport_injective act A E g hfix heq)
  · right
    refine ⟨?_, ?_⟩
    · intro hpq
      exact hne (congrArg g hpq)
    · intro c hp hq
      let d := c.transport g hfix
      have hpd : g p.1 ∈ d.carrier :=
        (Structure.BadCycleSequence.mem_transport_carrier_iff
          c g hfix p.1).2 hp
      have hqd : g q.1 ∈ d.carrier :=
        (Structure.BadCycleSequence.mem_transport_carrier_iff
          c g hfix q.1).2 hq
      have hpEval :
          (valuationPointTransport act A E g hfix p).2 ⟨d, hpd⟩ =
            p.2 ⟨c, hp⟩ :=
        valuationPointTransport_eval_image act A E g hfix p c hp
      have hqEval :
          (valuationPointTransport act A E g hfix q).2 ⟨d, hqd⟩ =
            q.2 ⟨c, hq⟩ :=
        valuationPointTransport_eval_image act A E g hfix q c hq
      rcases hcycles d hpd hqd with ⟨hnw, heq⟩ | ⟨hw, hneq⟩
      · left
        constructor
        · exact (Structure.BadCycleSequence.nonWrapPair_transport_iff
            c g hfix p.1 q.1).1 hnw
        · rw [hpEval, hqEval] at heq
          exact heq
      · right
        constructor
        · exact (Structure.BadCycleSequence.wrapPair_transport_iff
            c g hfix p.1 q.1).1 hw
        · rw [hpEval, hqEval] at hneq
          exact hneq

/-- Exact invariance of the genericity predicate under base transport. -/
theorem areGeneric_transport_iff
    (g : Structure.Automorphism act A)
    (hfix : act.FixesRel E)
    (p q : ValuationPoint A E) :
    AreGeneric A E
      (valuationPointTransport act A E g hfix p)
      (valuationPointTransport act A E g hfix q) ↔
      AreGeneric A E p q := by
  exact ⟨areGeneric_of_transport act A E g hfix,
    areGeneric_transport act A E g hfix⟩

end Sparsening
end AllThoseEPPA
