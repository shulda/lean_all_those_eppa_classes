import AllThoseEPPA.CycleSparseningBasics

/-!
# Clique closures and irreducibility for the chordal-cut argument

This is the structure-theoretic first step of Lemma `lem:cuts` in the
paper. For a distinguished binary relation `E`, the closure of an
E-clique is always irreducible, even in a language with set-valued
functions. The key point is that an E-clique cannot cross a free
amalgamation cut, and the closure of its generators is forced to
remain in the same side.

The following consequences localize relation tuples and function
values inside E-cliques whenever all irreducible substructures of
the ambient structure are E-cliques. These implications make the
graph-separator decomposition compatible with nontrivial functions.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A clique in the distinguished directed E-relation. The definition
does not assume E symmetric or loopless. In the cut lemma E will be
a symmetric simple graph. -/
def EdgeClique (B : Structure L V) (E : L.RelSymbol 2)
    (C : Set V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ C → y ∈ C → x ≠ y → B.Edge E x y

/-- In a free decomposition of a structure, an E-clique must lie
entirely on one of the two sides. No assumptions on arity of
function symbols are needed for this observation. -/
theorem edgeClique_subset_one_side
    (B : Structure L V) (E : L.RelSymbol 2)
    (d : B.FreeDecomposition)
    (C : Set V) (hC : EdgeClique B E C) :
    C ⊆ d.left ∨ C ⊆ d.right := by
  by_contra hnot
  have hnleft : ¬ C ⊆ d.left := by
    intro h
    exact hnot (Or.inl h)
  have hnright : ¬ C ⊆ d.right := by
    intro h
    exact hnot (Or.inr h)
  obtain ⟨x, hxC, hxL⟩ := Set.not_subset.mp hnleft
  obtain ⟨y, hyC, hyR⟩ := Set.not_subset.mp hnright
  have hxR : x ∈ d.right := by
    have hx : x ∈ d.left ∪ d.right := by
      rw [d.cover]
      exact Set.mem_univ x
    rcases hx with h | h
    · exact (hxL h).elim
    · exact h
  have hyL : y ∈ d.left := by
    have hy : y ∈ d.left ∪ d.right := by
      rw [d.cover]
      exact Set.mem_univ y
    rcases hy with h | h
    · exact h
    · exact (hyR h).elim
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hxL hyL
  have hrel : B.rel E (Structure.pairTuple x y) :=
    hC hxC hyC hxy
  rcases d.rel_local E (Structure.pairTuple x y) hrel with hl | hr
  · exact hxL (by simpa using hl (0 : Fin 2))
  · exact hyR (by simpa using hr (1 : Fin 2))

/-- **First structural ingredient of `lem:cuts`.**
The function closure of any E-clique is irreducible. In particular
the closure of a clique separator is a legitimate irreducible
substructure, rather than just a graph-theoretic separator. -/
theorem cliqueClosure_isIrreducible
    (B : Structure L V) (E : L.RelSymbol 2)
    (C : Set V) (hC : EdgeClique B E C) :
    (B.closureStructure C).IsIrreducible := by
  let S : Set V := B.closureSet C
  let hS : B.IsClosed S := B.isClosed_closureSet C
  change (B.induce S hS).IsIrreducible
  constructor
  intro d
  let CS : Set S := {x | (x : V) ∈ C}
  have hCS : EdgeClique (B.induce S hS) E CS := by
    intro x y hx hy hne
    have hxy : (x : V) ≠ (y : V) := by
      intro heq
      exact hne (Subtype.ext heq)
    have hedge : B.Edge E (x : V) (y : V) :=
      hC hx hy hxy
    change B.rel E (Subtype.val ∘ Structure.pairTuple x y)
    rw [Structure.pairTuple_map]
    exact hedge
  have absorb (T : Set S)
      (hT : (B.induce S hS).IsClosed T)
      (hct : CS ⊆ T) : T = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    have hClosed : B.IsClosed (Subtype.val '' T) :=
      Structure.isClosed_image_subtype B S hS T hT
    have hgenerators : C ⊆ Subtype.val '' T := by
      intro x hx
      let xS : S := ⟨x, B.subset_closureSet C hx⟩
      refine ⟨xS, ?_, rfl⟩
      exact hct (by simpa [CS, xS] using hx)
    have hz : z.1 ∈ Subtype.val '' T :=
      B.closureSet_minimal hClosed hgenerators z.2
    obtain ⟨t, ht, htz⟩ := hz
    have htzeq : t = z := Subtype.ext htz
    exact htzeq ▸ ht
  rcases edgeClique_subset_one_side (B.induce S hS) E d CS hCS with
      hleft | hright
  · exact d.left_proper (absorb d.left d.left_closed hleft)
  · exact d.right_proper (absorb d.right d.right_closed hright)

/-- The local hypothesis in `lem:cuts`: every irreducible closed
substructure is an E-clique. It follows from irreducible-structure
faithfulness of the EPPA witness when E is fixed by the language
action and is complete on A. -/
def IrreduciblesAreCliques
    (B : Structure L V) (E : L.RelSymbol 2) : Prop :=
  ∀ (S : Set V) (hS : B.IsClosed S),
    (B.induce S hS).IsIrreducible → EdgeClique B E S

/-- The closure of an E-clique is again an E-clique under the local
irreducibility hypothesis. -/
theorem closure_edgeClique
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    (C : Set V) (hC : EdgeClique B E C) :
    EdgeClique B E (B.closureSet C) :=
  hIrred (B.closureSet C) (B.isClosed_closureSet C)
    (cliqueClosure_isIrreducible B E C hC)

/-- Any two distinct vertices in a realized relation tuple are
E-adjacent if all irreducible substructures are E-cliques. This
uses irreducibility of the closure of a relation tuple, already
proved in the general EPPA API. -/
theorem relation_tuple_edge
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → V)
    (hrel : B.rel R xs) (i j : Fin n)
    (hij : xs i ≠ xs j) :
    B.Edge E (xs i) (xs j) := by
  let S : Set V := B.closureSet (Set.range xs)
  have hclosed : B.IsClosed S := B.isClosed_closureSet (Set.range xs)
  have hirr : (B.induce S hclosed).IsIrreducible :=
    B.relationTupleClosure_isIrreducible R xs hrel
  have hclique := hIrred S hclosed hirr
  apply hclique
  · exact B.subset_closureSet (Set.range xs) ⟨i, rfl⟩
  · exact B.subset_closureSet (Set.range xs) ⟨j, rfl⟩
  · exact hij

/-- A unary (in fact constant-tuple) function value is E-adjacent
to its input whenever the value is different from the input.
This follows because the one-point closure is irreducible. -/
theorem function_value_edge
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    {n : ℕ} (F : L.FuncSymbol n) (x y : V)
    (hy : y ∈ B.func F (fun _ => x))
    (hxy : x ≠ y) :
    B.Edge E x y := by
  have hclique : EdgeClique B E (B.closureAtSet x) :=
    hIrred (B.closureAtSet x) (B.isClosed_closureSet {x})
      (B.closureAt_isIrreducible x)
  have hyclosure : y ∈ B.closureAtSet x := by
    exact (B.isClosed_closureSet {x}) F (fun _ => x)
      (fun _ => B.mem_closureAtSet x) hy
  exact hclique (B.mem_closureAtSet x) hyclosure hxy

end TreeLike
end AllThoseEPPA
