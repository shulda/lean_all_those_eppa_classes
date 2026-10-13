import AllThoseEPPA.Applications.KOrientations.SecondStageSuccessorAxioms

/-!
# Exact one-point unary closures in the second-stage witness B₁

The unrestricted faithful B₁ witness has a single set-valued unary
function F. The previously proved reflexivity and transitivity show
that its one-point generated substructures are *exactly* the F-values.

This exactness is essential for the root support of a reconstructed
root vertex: support(inl x) = closureAtSet x = F(x). Thus no accidental
additional root points enter a singleton support by iterating F.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The unary successor value F(x) is itself closed under every
function of the auxiliary language (there is only the one unary F). -/
theorem faithful_auxiliary_successor_isClosed
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (x : W) :
    B.IsClosed (B.func AuxiliaryFunc.successor ![x]) := by
  intro n F xs hxs y hy
  cases F with
  | successor =>
      have htup : xs = ![xs 0] := by
        funext i
        fin_cases i
        rfl
      rw [htup] at hy
      exact faithful_auxiliary_successor_trans G k S B ι hFaith
        (hxs 0) hy

/-- Exact equality between the ambient one-point closure and
the unary successor value in a faithful auxiliary witness. -/
theorem faithful_auxiliary_closureAt_eq_successors
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (x : W) :
    B.closureAtSet x =
      B.func AuxiliaryFunc.successor ![x] := by
  apply Set.Subset.antisymm
  · apply B.closureSet_minimal
      (faithful_auxiliary_successor_isClosed G k S B ι hFaith x)
    intro y hy
    have heq : y = x := by simpa using hy
    subst y
    exact faithful_auxiliary_successor_self G k S B ι hFaith x
  · exact auxiliary_successorValue_subset_closureAt G k B x

/-- Every root-to-root edge gives inclusion of its target's
one-point closure into the source's one-point closure. -/
theorem faithful_auxiliary_edge_closure_monotone
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {x y : W}
    (hxy : B.rel AuxiliaryRel.edge ![x,y]) :
    B.closureAtSet y ⊆ B.closureAtSet x := by
  have hyF : y ∈ B.func AuxiliaryFunc.successor ![x] :=
    faithful_auxiliary_edge_mem_successors G k S B ι hFaith hxy
  have hycl : y ∈ B.closureAtSet x :=
    auxiliary_successorValue_subset_closureAt G k B x hyF
  exact B.closureAtSet_subset_of_mem hycl

end AllThoseEPPA.Applications.KOrientations
