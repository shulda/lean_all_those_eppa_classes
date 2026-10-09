import AllThoseEPPA.Examples.Hypergraph3K4Faithful

/-!
# Ordinary EPPA for K₄³-free 3-uniform hypergraphs

Independent, self-contained statement for readers: no project-private
EPPA notions occur in the conclusion. Unlike the unrestricted hypergraph
regression, this genuinely tests irreducible-structure faithfulness.

The previously proved `Hypergraph3.eppa` is retained unchanged.
-/

universe u

/-- Every finite 3-uniform hypergraph omitting K₄³ has an EPPA witness
which also omits K₄³. Ordinary EPPA, with no coherence requirement. -/
theorem Hypergraph3.eppaK4Free
    {α : Type u} [Finite α] (A : Hypergraph3 α)
    (hA : A.IsK4Free) :
    ∃ (β : Type u) (_ : Finite β)
      (B : Hypergraph3 β) (ι : α ↪ β),

      -- The witness contains no complete four-vertex 3-hypergraph.
      B.IsK4Free ∧

      -- The original hypergraph is an induced subhypergraph.
      (∀ a b c : α,
        A.edge {a, b, c} ↔
          B.edge {ι a, ι b, ι c}) ∧

      -- Every partial automorphism extends.
      (∀ (U V : Set α) (p : U ≃ V),
        (∀ a b c : U,
          A.edge {a.1, b.1, c.1} ↔
            A.edge {(p a).1, (p b).1, (p c).1}) →

        ∃ g : Equiv.Perm β,
          (∀ x y z : β,
            B.edge {x, y, z} ↔
              B.edge {g x, g y, g z}) ∧
          (∀ a : U,
            g (ι a.1) = ι ((p a).1))
      ) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  obtain ⟨β, hβ, B, ψ, hcoh, hfaith⟩ :=
    AllThoseEPPA.Faithful.finiteOrbitUnaryStructuresHaveFaithfulCoherentEPPA
      Bridge.action (Bridge.toStructure A) (Bridge.finiteOrbit A)
  letI : Finite β := hβ
  let H : Hypergraph3 β := Bridge.fromFaithfulStructure A B ψ hfaith
  refine ⟨β, hβ, H, ⟨ψ.toFun, ψ.injective⟩,
    Bridge.fromFaithfulStructure_k4Free A hA B ψ hfaith, ?_, ?_⟩
  · intro a b c
    let xs : Fin 3 → α := ![a, b, c]
    have h :
        A.edge (Set.range xs) ↔
          H.edge (Set.range (ψ.toFun ∘ xs)) := by
      calc
        A.edge (Set.range xs) ↔
            (Bridge.toStructure A).rel Bridge.RelSymbol.triple xs :=
          Iff.rfl
        _ ↔ B.rel Bridge.RelSymbol.triple (ψ.toFun ∘ xs) := by
          simpa only [Bridge.action_on_triple] using
            (ψ.map_rel_iff Bridge.RelSymbol.triple xs).symm
        _ ↔ H.edge (Set.range (ψ.toFun ∘ xs)) :=
          (Bridge.fromFaithfulStructure_edge_iff
            A B ψ hfaith (ψ.toFun ∘ xs)).symm
    have hrangeA : Set.range xs = ({a, b, c} : Set α) := by
      ext t
      simp [xs, Bridge.range_triple, or_assoc, or_comm, or_left_comm]
    have hrangeB :
        Set.range (ψ.toFun ∘ xs) =
          ({ψ.toFun a, ψ.toFun b, ψ.toFun c} : Set β) := by
      ext t
      simp [xs, Bridge.range_triple, Function.comp_def,
        or_assoc, or_comm, or_left_comm]
    rw [hrangeA, hrangeB] at h
    exact h
  · intro U V p hp
    rcases hcoh with ⟨e⟩
    let q := Bridge.partialAutomorphism A U V p hp
    have hw : AllThoseEPPA.Structure.IsEPPAWitness Bridge.action ψ :=
      AllThoseEPPA.Structure.CoherentExtension.isEPPAWitness
        Bridge.action e
    obtain ⟨g, hg⟩ := hw q
    refine ⟨g.toEquiv, ?_, ?_⟩
    · intro x y z
      let xs : Fin 3 → β := ![x, y, z]
      have h :
          H.edge (Set.range xs) ↔
            H.edge (Set.range (g ∘ xs)) := by
        rw [Bridge.fromFaithfulStructure_edge_iff A B ψ hfaith xs,
            Bridge.fromFaithfulStructure_edge_iff A B ψ hfaith (g ∘ xs)]
        simpa only [Bridge.action_on_triple] using
          (AllThoseEPPA.Structure.Automorphism.map_rel_iff
            g Bridge.RelSymbol.triple xs).symm
      have hrangeX : Set.range xs = ({x, y, z} : Set β) := by
        ext t
        simp [xs, Bridge.range_triple, or_assoc, or_comm, or_left_comm]
      have hrangeG :
          Set.range (g ∘ xs) =
            ({g.toEquiv x, g.toEquiv y, g.toEquiv z} : Set β) := by
        ext t
        simp [xs, Bridge.range_triple, Function.comp_def,
          AllThoseEPPA.Structure.Automorphism.toEquiv_apply,
          or_assoc, or_comm, or_left_comm]
      rw [hrangeX, hrangeG] at h
      exact h
    · intro a
      have ha : a.1 ∈ q.source := a.2
      have h := hg.2 a.1 ha
      change g (ψ a.1) = ψ (Bridge.partialEquiv U V p a.1) at h
      simpa [Bridge.partialEquiv_apply_of_mem p a.2,
        AllThoseEPPA.Structure.Automorphism.toEquiv_apply] using h
