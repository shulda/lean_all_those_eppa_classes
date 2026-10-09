import AllThoseEPPA.CycleSparseningBasics

/-!
# Distinguished edges in irreducible-structure faithful witnesses

The statement of Lemma `lem:sparsen` observes that when the distinguished
relation `E` is complete on the irreducible base structure, irreducible-
structure faithfulness forces `E` in the witness to be an undirected
loopless graph.  This file isolates that argument.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w z

variable {L : Language.{u}}
variable {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type z}
variable {act : L.Action Γ}

/-- The closure of the two endpoints of an edge is irreducible. -/
theorem edgeClosure_isIrreducible
    (A : Structure L V) (E : L.RelSymbol 2)
    {x y : V} (hxy : A.Edge E x y) :
    (A.closureStructure (Set.range (pairTuple x y))).IsIrreducible := by
  apply relationTupleClosure_isIrreducible A E (pairTuple x y)
  exact hxy

/-- In an irreducible-structure faithful witness, the two endpoints of every
realized distinguished edge can be moved simultaneously into the embedded
copy of the base structure. -/
theorem edge_movable_into_embedded_copy
    {A : Structure L V} {B : Structure L W}
    (ψ : Embedding act A B)
    (hfaith : IsIrreducibleStructureFaithful act ψ)
    (E : L.RelSymbol 2)
    {x y : W} (hxy : B.Edge E x y) :
    ∃ g : Automorphism act B, ∃ a b : V,
      g x = ψ a ∧ g y = ψ b := by
  let S : Set W :=
    B.closureSet (Set.range (pairTuple x y))
  have hS : B.IsClosed S := by
    dsimp [S]
    exact B.isClosed_closureSet _
  have hirr : (B.induce S hS).IsIrreducible := by
    change
      (B.closureStructure
        (Set.range (pairTuple x y))).IsIrreducible
    exact edgeClosure_isIrreducible B E hxy
  rcases hfaith S hS hirr with ⟨g, hg⟩
  have hxS : x ∈ S := by
    change x ∈ B.closureSet (Set.range (pairTuple x y))
    exact
      B.subset_closureSet (Set.range (pairTuple x y))
        ⟨0, by simp [pairTuple]⟩
  have hyS : y ∈ S := by
    change y ∈ B.closureSet (Set.range (pairTuple x y))
    exact
      B.subset_closureSet (Set.range (pairTuple x y))
        ⟨1, by simp [pairTuple]⟩
  rcases hg x hxS with ⟨a, hga⟩
  rcases hg y hyS with ⟨b, hgb⟩
  exact ⟨g, a, b, hga, hgb⟩

/-- A distinguished complete graph on the base remains loopless in every
irreducible-structure faithful witness. -/
theorem edgeLoopless_of_irreducibleFaithful_complete
    {A : Structure L V} {B : Structure L W}
    (ψ : Embedding act A B)
    (hfaith : IsIrreducibleStructureFaithful act ψ)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E) :
    B.EdgeLoopless E := by
  intro x hxx
  rcases
      edge_movable_into_embedded_copy
        ψ hfaith E hxx with
    ⟨g, a, b, hga, hgb⟩
  have hgedge : B.Edge E (g x) (g x) :=
    (Automorphism.edge_map_iff
      g E hfix x x).2 hxx
  have himage : B.Edge E (ψ a) (ψ b) := by
    rw [← hga, ← hgb]
    exact hgedge
  have hAedge : A.Edge E a b :=
    (Embedding.edge_map_iff
      ψ E hfix a b).1 himage
  have hab : a ≠ b :=
    (hcomplete a b).mp hAedge
  have habeq : a = b := by
    apply ψ.injective
    exact hga.symm.trans hgb
  exact hab habeq

/-- A distinguished complete graph on the base remains symmetric in every
irreducible-structure faithful witness. -/
theorem edgeSymmetric_of_irreducibleFaithful_complete
    {A : Structure L V} {B : Structure L W}
    (ψ : Embedding act A B)
    (hfaith : IsIrreducibleStructureFaithful act ψ)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E) :
    B.EdgeSymmetric E := by
  have hdir :
      ∀ {x y : W}, B.Edge E x y → B.Edge E y x := by
    intro x y hxy
    rcases
        edge_movable_into_embedded_copy
          ψ hfaith E hxy with
      ⟨g, a, b, hga, hgb⟩
    have hgedge : B.Edge E (g x) (g y) :=
      (Automorphism.edge_map_iff
        g E hfix x y).2 hxy
    have himage : B.Edge E (ψ a) (ψ b) := by
      rw [← hga, ← hgb]
      exact hgedge
    have hAxy : A.Edge E a b :=
      (Embedding.edge_map_iff
        ψ E hfix a b).1 himage
    have hab : a ≠ b :=
      (hcomplete a b).mp hAxy
    have hAyx : A.Edge E b a :=
      (hcomplete b a).2 hab.symm
    have himageRev : B.Edge E (ψ b) (ψ a) :=
      (Embedding.edge_map_iff
        ψ E hfix b a).2 hAyx
    have hgRev : B.Edge E (g y) (g x) := by
      rw [hgb, hga]
      exact himageRev
    exact
      (Automorphism.edge_map_iff
        g E hfix y x).1 hgRev
  intro x y
  exact ⟨hdir, hdir⟩

/-- The paper's observation before the sparsening construction: `E` becomes
a simple undirected graph in an irreducible-structure faithful witness. -/
theorem edgeSimple_of_irreducibleFaithful_complete
    {A : Structure L V} {B : Structure L W}
    (ψ : Embedding act A B)
    (hfaith : IsIrreducibleStructureFaithful act ψ)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E) :
    B.EdgeLoopless E ∧ B.EdgeSymmetric E :=
  ⟨edgeLoopless_of_irreducibleFaithful_complete
      ψ hfaith E hfix hcomplete,
    edgeSymmetric_of_irreducibleFaithful_complete
      ψ hfaith E hfix hcomplete⟩

end Structure
end AllThoseEPPA
