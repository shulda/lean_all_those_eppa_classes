import AllThoseEPPA.Irreducible

/-!
# Local consequences of irreducible-structure faithfulness

The two-stage EPPA application repeatedly moves a one-point closure,
or the closure of a realized relation tuple, into the distinguished
source copy by a total automorphism. These facts are already contained
in the checked general irreducibility API and should not be reproved
for each new application relation.

The lemmas here are universally quantified; their later use will
specialize first to the successor witness B0 and then to the
root-language witness B1.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v w z

variable {L : Language.{u}}
variable {Γ : Type v} [Group Γ]
variable {α : Type w} {β : Type z}

/-- Faithfulness moves every one-point closure into the source copy. -/
theorem faithful_moves_vertexClosure
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ι : Structure.Embedding act A B)
    (hFaithful : Structure.IsIrreducibleStructureFaithful act ι)
    (x : β) :
    ∃ g : Structure.Automorphism act B,
      ∀ y, y ∈ B.closureAtSet x → ∃ a : α, g y = ι a := by
  exact hFaithful (B.closureAtSet x)
    (B.isClosed_closureSet {x})
    (B.closureAt_isIrreducible x)

/-- Faithfulness moves the closure of any realized relation tuple
into the source copy. This is the transfer mechanism for graph edges,
R_P- and E_P-tuples. -/
theorem faithful_moves_relationClosure
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ι : Structure.Embedding act A B)
    (hFaithful : Structure.IsIrreducibleStructureFaithful act ι)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → β)
    (hrel : B.rel R xs) :
    ∃ g : Structure.Automorphism act B,
      ∀ y, y ∈ B.closureSet (Set.range xs) →
        ∃ a : α, g y = ι a := by
  exact hFaithful (B.closureSet (Set.range xs))
    (B.isClosed_closureSet (Set.range xs))
    (B.relationTupleClosure_isIrreducible R xs hrel)

end AllThoseEPPA.Applications.KOrientations
