import AllThoseEPPA.TreeLikeFreshBinaryPartialIso

/-!
# EPPA and coherent EPPA lift across complete fresh-E expansions

Every old-language partial automorphism is precisely a partial
automorphism of the complete fixed-E expansion: the source, range,
underlying partial equivalence and Γ-language component are unchanged.
A witness automorphism preserving the old language therefore preserves
the new complete E, and its extension square is the same square.

The same transport respects equivalence of partial automorphisms
and coherent triples, hence preserves *coherent* EPPA, not merely EPPA.
No finite-carrier or unary-function hypothesis is used.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

namespace PartialIsomorphism

/-- Equivalence of partial automorphisms is preserved under forgetting E,
including the language component and equality on the partial source. -/
theorem equivalent_forgetFixedBinary
    (act : L.Action Γ)
    {A : Structure L.withFixedBinaryRel V}
    (p q : PartialIsomorphism act.withFixedBinaryRel A A)
    (h : Equivalent p q) :
    Equivalent (p.forgetFixedBinary act) (q.forgetFixedBinary act) :=
  h

/-- The underlying coherent-triple condition only involves partial maps,
which the E-reduct does not change. -/
theorem coherentTriple_forgetFixedBinary
    (act : L.Action Γ)
    {A : Structure L.withFixedBinaryRel V}
    (f g h : PartialIsomorphism act.withFixedBinaryRel A A)
    (ht : CoherentTriple f g h) :
    CoherentTriple (f.forgetFixedBinary act)
      (g.forgetFixedBinary act) (h.forgetFixedBinary act) :=
  ht

end PartialIsomorphism

/-- If B is an EPPA witness of A, their expansions by the same fresh
complete E also form an EPPA witness with unchanged Γ-language components. -/
theorem isEPPAWitness_withCompleteFixedBinary
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (ψ : Embedding act A B)
    (hEPPA : IsEPPAWitness act ψ) :
    IsEPPAWitness act.withFixedBinaryRel
      (ψ.withCompleteFixedBinary act) := by
  intro p
  obtain ⟨g, hg⟩ := hEPPA (p.forgetFixedBinary act)
  refine ⟨g.withCompleteFixedBinary act, ?_⟩
  exact hg

namespace CoherentExtension

/-- A coherent extension system also lifts to the complete fresh-E
expansion. Equivalent partial maps and their coherent triples are
unchanged, while the selected full automorphisms preserve composition. -/
def withCompleteFixedBinary
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    {ψ : Embedding act A B}
    (h : CoherentExtension act ψ) :
    CoherentExtension act.withFixedBinaryRel
      (ψ.withCompleteFixedBinary act) where
  extension := fun p =>
    (h.extension (p.forgetFixedBinary act)).withCompleteFixedBinary act
  extension_spec := by
    intro p
    exact h.extension_spec (p.forgetFixedBinary act)
  respects_equivalent := by
    intro p q hpq
    have hOld : PartialIsomorphism.Equivalent
        (p.forgetFixedBinary act) (q.forgetFixedBinary act) :=
      PartialIsomorphism.equivalent_forgetFixedBinary act p q hpq
    exact congrArg (fun g => g.withCompleteFixedBinary act)
      (h.respects_equivalent
        (p.forgetFixedBinary act) (q.forgetFixedBinary act) hOld)
  coherent := by
    intro f g t ht
    have hOld : PartialIsomorphism.CoherentTriple
        (f.forgetFixedBinary act)
        (g.forgetFixedBinary act)
        (t.forgetFixedBinary act) :=
      PartialIsomorphism.coherentTriple_forgetFixedBinary act f g t ht
    have hc := h.coherent
      (f.forgetFixedBinary act)
      (g.forgetFixedBinary act)
      (t.forgetFixedBinary act) hOld
    exact (congrArg (fun z => z.withCompleteFixedBinary act) hc).trans
      (Automorphism.withCompleteFixedBinary_comp act
        (h.extension (g.forgetFixedBinary act))
        (h.extension (f.forgetFixedBinary act)))

end CoherentExtension

/-- Complete fresh-E expansion preserves the coherent EPPA property. -/
theorem isCoherentEPPAWitness_withCompleteFixedBinary
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (ψ : Embedding act A B)
    (h : IsCoherentEPPAWitness act ψ) :
    IsCoherentEPPAWitness act.withFixedBinaryRel
      (ψ.withCompleteFixedBinary act) := by
  obtain ⟨c⟩ := h
  exact ⟨c.withCompleteFixedBinary act⟩

end Structure
end AllThoseEPPA
