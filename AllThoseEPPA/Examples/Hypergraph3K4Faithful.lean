import AllThoseEPPA.Examples.Hypergraph3K4Basic
import AllThoseEPPA.Examples.Hypergraph3Faithful

/-!
# A faithful relational witness preserves K₄³-freeness

This is the genuinely faithfulness-dependent part of the regression test:
the four vertices of a forbidden tetrahedron form an irreducible induced
substructure, so faithfulness transports that entire tetrahedron into the
distinguished copy of the original hypergraph.
-/

namespace Hypergraph3.Bridge

open AllThoseEPPA

universe u v

/-- A set containing four vertices has a third vertex different from any
two specified vertices. -/
private theorem exists_third_of_ncard_four {β : Type*}
    (S : Set β) (h4 : S.ncard = 4) (x y : S) :
    ∃ z : S, z ≠ x ∧ z ≠ y := by
  classical
  by_contra hz
  have hsub : S ⊆ ({x.1, y.1} : Set β) := by
    intro z hzS
    by_contra hn
    apply hz
    refine ⟨⟨z, hzS⟩, ?_, ?_⟩
    · intro h
      apply hn
      have he : z = x.1 := congrArg Subtype.val h
      simp [he]
    · intro h
      apply hn
      have he : z = y.1 := congrArg Subtype.val h
      simp [he]
  have hle : S.ncard ≤ ({x.1, y.1} : Set β).ncard :=
    Set.ncard_le_ncard hsub
  have hpair : ({x.1, y.1} : Set β).ncard ≤ 2 := by
    calc
      _ ≤ ({y.1} : Set β).ncard + 1 := Set.ncard_insert_le x.1 {y.1}
      _ = 2 := by simp
  have hbad : (4 : ℕ) ≤ 2 := by
    calc
      4 = S.ncard := h4.symm
      _ ≤ ({x.1, y.1} : Set β).ncard := hle
      _ ≤ 2 := hpair
  exact (by decide : ¬ (4 : ℕ) ≤ 2) hbad

/-- Every induced complete 3-uniform hypergraph on four vertices is
irreducible as a relational structure. -/
theorem k4Induced_isIrreducible
    {β : Type*} (B : AllThoseEPPA.Structure language β)
    (S : Set β) (h4 : S.ncard = 4)
    (hfull : ∀ xs : Fin 3 → β,
      Set.range xs ⊆ S →
      (Set.range xs).ncard = 3 →
      B.rel RelSymbol.triple xs)
    (hclosed : B.IsClosed S) :
    (B.induce S hclosed).IsIrreducible := by
  classical
  constructor
  intro d
  have hleft : ∃ x : S, x ∉ d.left := by
    by_contra h
    apply d.left_proper
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  have hright : ∃ y : S, y ∉ d.right := by
    by_contra h
    apply d.right_proper
    apply Set.eq_univ_of_forall
    intro y
    by_contra hy
    exact h ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hleft
  obtain ⟨y, hy⟩ := hright
  have hxy : x ≠ y := by
    intro he
    subst y
    have hcover : x ∈ d.left ∪ d.right := by
      rw [d.cover]
      exact Set.mem_univ _
    rcases hcover with hxl | hyr
    · exact hx hxl
    · exact hy hyr
  obtain ⟨z, hzx, hzy⟩ := exists_third_of_ncard_four S h4 x y
  let xs : Fin 3 → S := ![x, y, z]
  have hsub : Set.range (Subtype.val ∘ xs) ⊆ S := by
    rintro w ⟨i, rfl⟩
    exact (xs i).property
  have h3 : (Set.range (Subtype.val ∘ xs)).ncard = 3 := by
    rw [Set.range_comp, Set.ncard_image_of_injective _ Subtype.val_injective]
    rw [range_triple]
    exact (Set.ncard_eq_three).2
      ⟨x, y, z, hxy, hzx.symm, hzy.symm, rfl⟩
  have hrel : (B.induce S hclosed).rel RelSymbol.triple xs :=
    hfull (Subtype.val ∘ xs) hsub h3
  rcases d.rel_local RelSymbol.triple xs hrel with hl | hr
  · exact hx (hl 0)
  · exact hy (hr 1)

/-- In an irreducible-structure faithful EPPA witness, no new K₄³ can
appear if the base hypergraph has none. -/
theorem fromFaithfulStructure_k4Free
    {α : Type u} {β : Type v}
    (A : Hypergraph3 α) (hA : A.IsK4Free)
    (B : AllThoseEPPA.Structure language β)
    (ψ : AllThoseEPPA.Structure.Embedding action (toStructure A) B)
    (hfaith : AllThoseEPPA.Structure.IsIrreducibleStructureFaithful action ψ) :
    (fromFaithfulStructure A B ψ hfaith).IsK4Free := by
  classical
  intro S h4 hfull
  have hclosed : B.IsClosed S := by
    intro n F xs hxs y hy
    exact F.elim
  have hfullRel :
      ∀ xs : Fin 3 → β, Set.range xs ⊆ S →
        (Set.range xs).ncard = 3 → B.rel RelSymbol.triple xs := by
    intro xs hsub h3
    exact (fromFaithfulStructure_edge_iff A B ψ hfaith xs).1
      (hfull (Set.range xs) hsub h3)
  have hirr : (B.induce S hclosed).IsIrreducible :=
    k4Induced_isIrreducible B S h4 hfullRel hclosed
  obtain ⟨g, hmove⟩ := hfaith S hclosed hirr
  let pre (x : S) : α := Classical.choose (hmove x.1 x.2)
  have hpre (x : S) : g x.1 = ψ (pre x) :=
    Classical.choose_spec (hmove x.1 x.2)
  have hpreinj : Function.Injective pre := by
    intro x y hxy
    apply Subtype.ext
    apply g.toEquiv.injective
    change g x.1 = g y.1
    rw [hpre x, hpre y, hxy]
  have hT4 : (Set.range pre).ncard = 4 := by
    calc
      (Set.range pre).ncard = Nat.card S :=
        Set.ncard_range_of_injective hpreinj
      _ = S.ncard := Nat.card_coe_set_eq S
      _ = 4 := h4
  apply hA (Set.range pre) hT4
  intro T hTsub hT3
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
    (Set.ncard_eq_three).1 hT3
  have ha : a ∈ Set.range pre := hTsub (by simp)
  have hb : b ∈ Set.range pre := hTsub (by simp)
  have hc : c ∈ Set.range pre := hTsub (by simp)
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  obtain ⟨z, hz⟩ := hc
  have hxy : x.1 ≠ y.1 := by
    intro he
    apply hab
    calc
      a = pre x := hx.symm
      _ = pre y := congrArg pre (Subtype.ext he)
      _ = b := hy
  have hxz : x.1 ≠ z.1 := by
    intro he
    apply hac
    calc
      a = pre x := hx.symm
      _ = pre z := congrArg pre (Subtype.ext he)
      _ = c := hz
  have hyz : y.1 ≠ z.1 := by
    intro he
    apply hbc
    calc
      b = pre y := hy.symm
      _ = pre z := congrArg pre (Subtype.ext he)
      _ = c := hz
  let xs : Fin 3 → β := ![x.1, y.1, z.1]
  let ys : Fin 3 → α := ![pre x, pre y, pre z]
  have hsub : Set.range xs ⊆ S := by
    rintro w ⟨i, rfl⟩
    fin_cases i
    · exact x.2
    · exact y.2
    · exact z.2
  have h3 : (Set.range xs).ncard = 3 := by
    have hs : Set.range xs = ({x.1, y.1, z.1} : Set β) := by
      ext t
      simp [xs, range_triple, or_assoc, or_comm, or_left_comm]
    rw [hs]
    exact (Set.ncard_eq_three).2
      ⟨x.1, y.1, z.1, hxy, hxz, hyz, rfl⟩
  have hrel : B.rel RelSymbol.triple xs := hfullRel xs hsub h3
  have hrelg : B.rel RelSymbol.triple (g ∘ xs) := by
    simpa only [action_on_triple] using
      ((AllThoseEPPA.Structure.Automorphism.map_rel_iff
        g RelSymbol.triple xs).2 hrel)
  have hcomp : (g ∘ xs) = (ψ.toFun ∘ ys) := by
    funext i
    fin_cases i
    · simpa [xs, ys, Function.comp_def] using hpre x
    · simpa [xs, ys, Function.comp_def] using hpre y
    · simpa [xs, ys, Function.comp_def] using hpre z
  rw [hcomp] at hrelg
  have hAedge : A.edge (Set.range ys) := by
    change (toStructure A).rel RelSymbol.triple ys
    apply (ψ.map_rel_iff RelSymbol.triple ys).1
    simpa only [action_on_triple] using hrelg
  have hrange :
      Set.range ys = ({a, b, c} : Set α) := by
    ext t
    simp [ys, range_triple, hx, hy, hz,
      or_assoc, or_comm, or_left_comm]
  rw [hrange] at hAedge
  exact hAedge

end Hypergraph3.Bridge
