import AllThoseEPPA.CycleSparseningIndexTransport

/-!
# Genericity under transport of bad-cycle valuations

Unlike the faithful-label construction, the fibres here are Boolean. The
proof uses the equivariant indexing of bad cycles and the fact that the
ordered closing edge is fixed by automorphism transport. No additional
label-completion argument is necessary.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w

variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w}
variable (act : L.Action Γ) (A : Structure L V) (E : L.RelSymbol 2)

/-- Evaluate a transported valuation at a target bad cycle, by pulling
that cycle back through the inverse automorphism. -/
theorem valuationPointTransport_eval
    (g : Structure.Automorphism act A)
    (hfix : act.FixesRel E)
    (p : ValuationPoint A E)
    (c : Structure.BadCycleSequence A E)
    (hp : g p.1 ∈ c.carrier) :
    let d := c.transport g.symm hfix
    let hd : p.1 ∈ d.carrier := by
      rcases hp with ⟨i, hi⟩
      exact ⟨i, by
        change g.symm (c.vertex i) = p.1
        rw [hi]
        simp⟩
    (valuationPointTransport act A E g hfix p).2 ⟨c, hp⟩ =
      p.2 ⟨d, hd⟩ := by
  dsimp only
  let d := c.transport g.symm hfix
  have hd : p.1 ∈ d.carrier := by
    rcases hp with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change g.symm (c.vertex i) = p.1
    rw [hi]
    simp
  have hcycle : d.transport g hfix = c :=
    Structure.BadCycleSequence.transport_transport_symm c g hfix
  have hindex :
      badCyclesAtEquiv act A E g hfix p.1 ⟨d, hd⟩ =
        (⟨c, hp⟩ : BadCyclesAt A E (g p.1)) := by
    apply Subtype.ext
    exact hcycle
  change
    valuationFunctionTransportEquiv act A E g hfix p.1 p.2 ⟨c, hp⟩ =
      p.2 ⟨d, hd⟩
  rw [← hindex]
  exact valuationFunctionTransportEquiv_apply_transport
    act A E g hfix p.1 p.2 ⟨d, hd⟩

/-- Genericity is preserved by transporting cycle-valued points through
any automorphism fixing the distinguished relation E. -/
theorem areGeneric_transport
    (g : Structure.Automorphism act A)
    (hfix : act.FixesRel E)
    {p q : ValuationPoint A E}
    (hgen : AreGeneric A E p q) :
    AreGeneric A E
      (valuationPointTransport act A E g hfix p)
      (valuationPointTransport act A E g hfix q) := by
  rcases hgen with heq | ⟨hne, hcycles⟩
  · exact Or.inl (congrArg (valuationPointTransport act A E g hfix) heq)
  · right
    refine ⟨?_, ?_⟩
    · change g p.1 ≠ g q.1
      exact fun h => hne (g.toEquiv.injective h)
    · intro c hp hq
      let d := c.transport g.symm hfix
      have hpd : p.1 ∈ d.carrier := by
        rcases hp with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        change g.symm (c.vertex i) = p.1
        rw [hi]
        simp
      have hqd : q.1 ∈ d.carrier := by
        rcases hq with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        change g.symm (c.vertex i) = q.1
        rw [hi]
        simp
      have hdc : d.transport g hfix = c :=
        Structure.BadCycleSequence.transport_transport_symm c g hfix
      have hpEval :
          (valuationPointTransport act A E g hfix p).2 ⟨c, hp⟩ =
            p.2 ⟨d, hpd⟩ := by
        exact valuationPointTransport_eval act A E g hfix p c hp
      have hqEval :
          (valuationPointTransport act A E g hfix q).2 ⟨c, hq⟩ =
            q.2 ⟨d, hqd⟩ := by
        exact valuationPointTransport_eval act A E g hfix q c hq
      rcases hcycles d hpd hqd with ⟨hnw, heq⟩ | ⟨hw, hnebits⟩
      · left
        constructor
        · have ht := (Structure.BadCycleSequence.nonWrapPair_transport_iff
              d g hfix p.1 q.1).2 hnw
          rw [hdc] at ht
          exact ht
        · rw [hpEval, hqEval]
          exact heq
      · right
        constructor
        · have ht := (Structure.BadCycleSequence.wrapPair_transport_iff
              d g hfix p.1 q.1).2 hw
          rw [hdc] at ht
          exact ht
        · rw [hpEval, hqEval]
          exact hnebits

end Sparsening
end AllThoseEPPA
