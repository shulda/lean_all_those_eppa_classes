import AllThoseEPPA.CycleSparseningValuations

/-!
# Genericity for cycle valuations

The genericity rule is the one from Section `sec:cycles`: on an ordinary
consecutive edge of a bad cycle the two bits agree, while on the closing
(first/last) edge they disagree.
-/

namespace AllThoseEPPA
namespace Structure

universe u v

/-- Adjacency in the displayed linear order of a cycle sequence, i.e. an edge
between consecutive entries which is not the cyclic wrap edge. -/
def LinearAdjacent {k : ℕ} (i j : Fin k) : Prop :=
  j.1 = i.1 + 1 ∨ i.1 = j.1 + 1

theorem linearAdjacent_symm {k : ℕ} (i j : Fin k) :
    LinearAdjacent i j ↔ LinearAdjacent j i := by
  constructor <;> intro h
  · rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h

namespace BadCycleSequence

variable {L : Language.{u}} {V : Type v}
variable {A : Structure L V} {E : L.RelSymbol 2}

/-- Two vertices form one of the non-wrap consecutive edges in the displayed
bad cycle sequence. -/
def NonWrapPair (c : BadCycleSequence A E) (x y : V) : Prop :=
  ∃ i j : Fin c.length,
    c.vertex i = x ∧
    c.vertex j = y ∧
    CyclicAdjacent i j ∧
    LinearAdjacent i j

/-- Two vertices form the cyclic closing edge, rather than a consecutive edge
in the displayed linear order. -/
def WrapPair (c : BadCycleSequence A E) (x y : V) : Prop :=
  ∃ i j : Fin c.length,
    c.vertex i = x ∧
    c.vertex j = y ∧
    CyclicAdjacent i j ∧
    ¬ LinearAdjacent i j

theorem nonWrapPair_symm
    (c : BadCycleSequence A E) (x y : V) :
    c.NonWrapPair x y ↔ c.NonWrapPair y x := by
  constructor
  · rintro ⟨i, j, hix, hjy, hcyc, hlin⟩
    exact
      ⟨j, i, hjy, hix,
        (cyclicAdjacent_symm i j).1 hcyc,
        (linearAdjacent_symm i j).1 hlin⟩
  · rintro ⟨i, j, hiy, hjx, hcyc, hlin⟩
    exact
      ⟨j, i, hjx, hiy,
        (cyclicAdjacent_symm i j).1 hcyc,
        (linearAdjacent_symm i j).1 hlin⟩

theorem wrapPair_symm
    (c : BadCycleSequence A E) (x y : V) :
    c.WrapPair x y ↔ c.WrapPair y x := by
  constructor
  · rintro ⟨i, j, hix, hjy, hcyc, hnlin⟩
    refine
      ⟨j, i, hjy, hix,
        (cyclicAdjacent_symm i j).1 hcyc, ?_⟩
    intro hlin
    exact hnlin ((linearAdjacent_symm i j).2 hlin)
  · rintro ⟨i, j, hiy, hjx, hcyc, hnlin⟩
    refine
      ⟨j, i, hjx, hiy,
        (cyclicAdjacent_symm i j).1 hcyc, ?_⟩
    intro hlin
    exact hnlin ((linearAdjacent_symm i j).2 hlin)

end BadCycleSequence
end Structure

namespace Sparsening

universe u v

variable {L : Language.{u}}
variable {V : Type v}
variable (A : Structure L V)
variable (E : L.RelSymbol 2)

/-- Genericity of two cycle-valuation points.  Equal points are allowed.
For distinct base vertices, every common bad cycle must make them adjacent:
ordinary consecutive edges carry equal bits and the wrap edge carries
different bits. -/
def AreGeneric
    (p q : ValuationPoint A E) : Prop :=
  p = q ∨
    (p.1 ≠ q.1 ∧
      ∀ (c : Structure.BadCycleSequence A E)
        (hp : p.1 ∈ c.carrier) (hq : q.1 ∈ c.carrier),
        (c.NonWrapPair p.1 q.1 ∧
            p.2 ⟨c, hp⟩ = q.2 ⟨c, hq⟩) ∨
        (c.WrapPair p.1 q.1 ∧
            p.2 ⟨c, hp⟩ ≠ q.2 ⟨c, hq⟩))

/-- A set of cycle-valuation points is generic when every pair is generic. -/
def IsGeneric
    (S : Set (ValuationPoint A E)) : Prop :=
  ∀ ⦃p⦄, p ∈ S → ∀ ⦃q⦄, q ∈ S →
    AreGeneric A E p q

theorem areGeneric_refl
    (p : ValuationPoint A E) :
    AreGeneric A E p p :=
  Or.inl rfl

theorem areGeneric_symm
    {p q : ValuationPoint A E}
    (h : AreGeneric A E p q) :
    AreGeneric A E q p := by
  rcases h with hpq | ⟨hne, hcycles⟩
  · exact Or.inl hpq.symm
  · refine Or.inr ⟨hne.symm, ?_⟩
    intro c hq hp
    rcases hcycles c hp hq with
      ⟨hnw, hbit⟩ | ⟨hwrap, hbit⟩
    · exact
        Or.inl
          ⟨(c.nonWrapPair_symm p.1 q.1).1 hnw,
            hbit.symm⟩
    · exact
        Or.inr
          ⟨(c.wrapPair_symm p.1 q.1).1 hwrap,
            Ne.symm hbit⟩

/-- Distinct generic valuation points which lie on a common bad cycle are
joined by an `E`-edge.  This is the basic local mechanism by which genericity
unwinds induced cycles. -/
theorem edge_of_areGeneric_of_common_cycle
    {p q : ValuationPoint A E}
    (hgen : AreGeneric A E p q)
    (hne : p.1 ≠ q.1)
    (c : Structure.BadCycleSequence A E)
    (hp : p.1 ∈ c.carrier)
    (hq : q.1 ∈ c.carrier) :
    A.Edge E p.1 q.1 := by
  rcases hgen with hpq | ⟨_, hcycles⟩
  · exact False.elim (hne (congrArg Sigma.fst hpq))
  · rcases hcycles c hp hq with
      ⟨hnw, _⟩ | ⟨hwrap, _⟩
    · rcases hnw with
        ⟨i, j, hix, hjy, hcyc, _⟩
      have hedge :=
        (c.edge_iff i j).2 hcyc
      rw [hix, hjy] at hedge
      exact hedge
    · rcases hwrap with
        ⟨i, j, hix, hjy, hcyc, _⟩
      have hedge :=
        (c.edge_iff i j).2 hcyc
      rw [hix, hjy] at hedge
      exact hedge

end Sparsening
end AllThoseEPPA
