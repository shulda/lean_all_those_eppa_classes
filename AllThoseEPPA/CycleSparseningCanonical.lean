import AllThoseEPPA.CycleSparseningCycleGraph
import AllThoseEPPA.Faithful

/-!
# Canonical embedded copy for cycle sparsening

This file starts the formalization of Claim `c:cycles:emb`.  The first
ingredient is the paper's observation that, because the distinguished
relation is complete on the embedded copy of `A`, any two distinct embedded
vertices lying on the same bad induced cycle must be adjacent on that cycle.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w z

variable {L : Language.{u}}
variable {Γ : Type v} [Group Γ]
variable {α : Type w}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α)
variable (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)
variable (E : L.RelSymbol 2)

/-- Two distinct vertices from the embedded complete `E`-copy of `A`
which occur on a common bad cycle are consecutive on that cycle; according
to the displayed linear order this is either a non-wrap or the wrap edge. -/
theorem embedded_common_cycle_pair_classified
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (c : Structure.BadCycleSequence B₀ E)
    {a b : α}
    (hab : a ≠ b)
    (ha : ψ a ∈ c.carrier)
    (hb : ψ b ∈ c.carrier) :
    c.NonWrapPair (ψ a) (ψ b) ∨
      c.WrapPair (ψ a) (ψ b) := by
  have hAedge : A.Edge E a b :=
    (hcomplete a b).2 hab
  have hBedge : B₀.Edge E (ψ a) (ψ b) :=
    (Structure.Embedding.edge_map_iff
      ψ E hfix a b).2 hAedge
  rcases ha with ⟨i, hi⟩
  rcases hb with ⟨j, hj⟩
  have hedge :
      B₀.Edge E (c.vertex i) (c.vertex j) := by
    rw [hi, hj]
    exact hBedge
  have hcyc : Structure.CyclicAdjacent i j :=
    (c.edge_iff i j).1 hedge
  by_cases hlin : Structure.LinearAdjacent i j
  · exact Or.inl ⟨i, j, hi, hj, hcyc, hlin⟩
  · exact Or.inr ⟨i, j, hi, hj, hcyc, hlin⟩


/-- An induced bad cycle cannot contain three distinct vertices of the
embedded complete distinguished relation.  In the graph-theoretic language,
the copy of A is a clique whereas an induced cycle of length >= 4 is
triangle-free. -/
theorem embedded_bad_cycle_no_three
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (c : Structure.BadCycleSequence B₀ E)
    {a b d : α}
    (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (ha : ψ a ∈ c.carrier)
    (hb : ψ b ∈ c.carrier)
    (hd : ψ d ∈ c.carrier) : False := by
  rcases ha with ⟨i, hi⟩
  rcases hb with ⟨j, hj⟩
  rcases hd with ⟨l, hl⟩
  have hij : B₀.Edge E (c.vertex i) (c.vertex j) := by
    rw [hi, hj]
    exact (Structure.Embedding.edge_map_iff ψ E hfix a b).2
      ((hcomplete a b).2 hab)
  have hjl : B₀.Edge E (c.vertex j) (c.vertex l) := by
    rw [hj, hl]
    exact (Structure.Embedding.edge_map_iff ψ E hfix b d).2
      ((hcomplete b d).2 hbd)
  have hli : B₀.Edge E (c.vertex l) (c.vertex i) := by
    rw [hl, hi]
    exact (Structure.Embedding.edge_map_iff ψ E hfix d a).2
      ((hcomplete d a).2 hda)
  exact c.no_edge_triangle i j l hij hjl hli


/-- The canonical 0/1 valuation from Section `sec:cycles`: only the first
vertex of a displayed bad cycle receives bit 1, and only when the last
vertex also lies in the distinguished copy.  The definition is valid at
arbitrary base vertices, but its genericity is proved on the embedded copy. -/
noncomputable def canonicalValuationFunction (x : β) :
    ValuationFunction B₀ E x := by
  classical
  exact fun c =>
    decide (c.1.firstVertex = x ∧ c.1.lastVertex ∈ Set.range ψ)

noncomputable def canonicalValuationPoint (x : β) :
    ValuationPoint B₀ E :=
  ⟨x, canonicalValuationFunction act A B₀ ψ E x⟩

/-- Given two distinct distinguished vertices on a bad cycle, every other
distinguished vertex on that cycle is one of those two. -/
theorem embedded_cycle_point_eq_left_or_right
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (c : Structure.BadCycleSequence B₀ E)
    {a b : α} (hab : a ≠ b)
    (ha : ψ a ∈ c.carrier)
    (hb : ψ b ∈ c.carrier)
    {x : β}
    (hxA : x ∈ Set.range ψ)
    (hxC : x ∈ c.carrier) :
    x = ψ a ∨ x = ψ b := by
  rcases hxA with ⟨d, rfl⟩
  by_cases hda : d = a
  · exact Or.inl (congrArg ψ hda)
  by_cases hdb : d = b
  · exact Or.inr (congrArg ψ hdb)
  exact (embedded_bad_cycle_no_three
    act A B₀ ψ E hfix hcomplete c
    hab (Ne.symm hdb) hda ha hb hxC).elim

/-- The canonical valuations agree along non-closing adjacent pairs from
the distinguished copy. -/
theorem canonicalBits_nonWrap
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (c : Structure.BadCycleSequence B₀ E)
    {a b : α} (hab : a ≠ b)
    (ha : ψ a ∈ c.carrier)
    (hb : ψ b ∈ c.carrier)
    (hnw : c.NonWrapPair (ψ a) (ψ b)) :
    canonicalValuationFunction act A B₀ ψ E (ψ a) ⟨c, ha⟩ =
      canonicalValuationFunction act A B₀ ψ E (ψ b) ⟨c, hb⟩ := by
  classical
  have hnotwrap : ¬ c.WrapPair (ψ a) (ψ b) :=
    c.nonWrapPair_not_wrap hnw
  by_cases hlast : c.lastVertex ∈ Set.range ψ
  · have hlastC : c.lastVertex ∈ c.carrier :=
      ⟨c.lastIndex, rfl⟩
    rcases (embedded_cycle_point_eq_left_or_right
      act A B₀ ψ E hfix hcomplete c hab ha hb
      hlast hlastC) with hla | hlb
    · have hfa : c.firstVertex ≠ ψ a := by
        intro h
        exact c.firstVertex_ne_lastVertex (h.trans hla.symm)
      have hfb : c.firstVertex ≠ ψ b := by
        intro h
        apply hnotwrap
        apply (c.wrapPair_iff_ends (ψ a) (ψ b)).2
        exact Or.inr ⟨hla.symm, h.symm⟩
      simp [canonicalValuationFunction, hfa, hfb]
    · have hfb : c.firstVertex ≠ ψ b := by
        intro h
        exact c.firstVertex_ne_lastVertex (h.trans hlb.symm)
      have hfa : c.firstVertex ≠ ψ a := by
        intro h
        apply hnotwrap
        apply (c.wrapPair_iff_ends (ψ a) (ψ b)).2
        exact Or.inl ⟨h.symm, hlb.symm⟩
      simp [canonicalValuationFunction, hfa, hfb]
  · simp [canonicalValuationFunction, hlast]

/-- The canonical valuations disagree along the unique closing edge. -/
theorem canonicalBits_wrap
    (c : Structure.BadCycleSequence B₀ E)
    {a b : α}
    (ha : ψ a ∈ c.carrier)
    (hb : ψ b ∈ c.carrier)
    (hw : c.WrapPair (ψ a) (ψ b)) :
    canonicalValuationFunction act A B₀ ψ E (ψ a) ⟨c, ha⟩ ≠
      canonicalValuationFunction act A B₀ ψ E (ψ b) ⟨c, hb⟩ := by
  classical
  rcases (c.wrapPair_iff_ends (ψ a) (ψ b)).1 hw with
      ⟨hfa, hlb⟩ | ⟨hla, hfb⟩
  · have hlast : c.lastVertex ∈ Set.range ψ := ⟨b, hlb⟩
    have hfirstA : c.firstVertex = ψ a := hfa.symm
    have hfirstB : c.firstVertex ≠ ψ b := by
      intro h
      exact c.firstVertex_ne_lastVertex (h.trans hlb)
    have hab' : ψ a ≠ ψ b := by
      intro h
      exact hfirstB (hfirstA.trans h)
    simp [canonicalValuationFunction, hlast, hfirstA, hab']
  · have hlast : c.lastVertex ∈ Set.range ψ := ⟨a, hla⟩
    have hfirstB : c.firstVertex = ψ b := hfb.symm
    have hfirstA : c.firstVertex ≠ ψ a := by
      intro h
      exact c.firstVertex_ne_lastVertex (h.trans hla)
    have hba' : ψ b ≠ ψ a := by
      intro h
      exact hfirstA (hfirstB.trans h)
    simp [canonicalValuationFunction, hlast, hfirstB, hba']

/-- The canonical valuation points corresponding to vertices of A are
pairwise generic, for the precise cycle-genericity predicate. -/
theorem canonical_areGeneric
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (a b : α) :
    AreGeneric B₀ E
      (canonicalValuationPoint act A B₀ ψ E (ψ a))
      (canonicalValuationPoint act A B₀ ψ E (ψ b)) := by
  by_cases hab : a = b
  · subst b
    exact areGeneric_refl B₀ E
      (canonicalValuationPoint act A B₀ ψ E (ψ a))
  · refine Or.inr ⟨?_, ?_⟩
    · intro h
      have hbase : ψ a = ψ b := by
        exact congrArg
          (fun p : ValuationPoint B₀ E => p.1) h
      exact hab (ψ.injective hbase)
    · intro c ha hb
      rcases (embedded_common_cycle_pair_classified
        act A B₀ ψ E hfix hcomplete c hab ha hb) with hnw | hw
      · exact Or.inl
          ⟨hnw, canonicalBits_nonWrap
            act A B₀ ψ E hfix hcomplete c hab ha hb hnw⟩
      · exact Or.inr
          ⟨hw, canonicalBits_wrap act A B₀ ψ E c ha hb hw⟩

/-- The canonical valuation assignment on the one-point closure of a
distinguished vertex is pairwise generic. -/
noncomputable def canonicalValuationStructure
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (a : α) :
    ValuationStructure B₀ E (ψ a) := by
  classical
  have hsub : B₀.closureAtSet (ψ a) ⊆ Set.range ψ :=
    Faithful.closureAtSet_subset_embedding_range
      act A B₀ ψ ⟨a, rfl⟩
  refine ⟨fun y => canonicalValuationFunction act A B₀ ψ E y.1, ?_⟩
  intro y z
  rcases hsub y.2 with ⟨a', ha'⟩
  rcases hsub z.2 with ⟨b', hb'⟩
  change AreGeneric B₀ E
    (canonicalValuationPoint act A B₀ ψ E y.1)
    (canonicalValuationPoint act A B₀ ψ E z.1)
  rw [← ha', ← hb']
  exact canonical_areGeneric
    act A B₀ ψ E hfix hcomplete a' b'

/-- Canonical valuation structures are stable under restriction to
one-point closures, which is needed for the function part of the embedding. -/
theorem canonicalValuationStructure_restrict
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (a b : α)
    (hb : ψ b ∈ B₀.closureAtSet (ψ a)) :
    (canonicalValuationStructure
      act A B₀ ψ E hfix hcomplete a).restrict
        B₀ E (ψ b) hb =
      canonicalValuationStructure act A B₀ ψ E hfix hcomplete b := by
  apply Subtype.ext
  funext z
  rfl

/-- The distinguished copy of A as vertices of the cycle-sparsening witness. -/
noncomputable def canonicalVertex
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (a : α) :
    WitnessVertex B₀ E :=
  ⟨ψ a, canonicalValuationStructure
    act A B₀ ψ E hfix hcomplete a⟩

/-- Every family of canonical witness vertices is generic, including all
valuation points in their one-point closures. -/
theorem canonicalFamilyGeneric
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    {ι : Type*} (as : ι → α) :
    WitnessFamilyGeneric B₀ E
      (fun i => canonicalVertex
        act A B₀ ψ E hfix hcomplete (as i)) := by
  intro i j y z
  have hy : y.1 ∈ Set.range ψ :=
    Faithful.closureAtSet_subset_embedding_range
      act A B₀ ψ ⟨as i, rfl⟩ y.2
  have hz : z.1 ∈ Set.range ψ :=
    Faithful.closureAtSet_subset_embedding_range
      act A B₀ ψ ⟨as j, rfl⟩ z.2
  rcases hy with ⟨a, ha⟩
  rcases hz with ⟨b, hb⟩
  change AreGeneric B₀ E
    (canonicalValuationPoint act A B₀ ψ E y.1)
    (canonicalValuationPoint act A B₀ ψ E z.1)
  rw [← ha, ← hb]
  exact canonical_areGeneric
    act A B₀ ψ E hfix hcomplete a b

end Sparsening
end AllThoseEPPA
