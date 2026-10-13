import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportMonotone

/-!
# One direction of exact reconstructed root supports

The certified orientation construction intends B₁ itself to be the
root sort. Before proving the (outdegree-defined) root predicate
identifies exactly B₁, one can already prove the unconditional
path-theoretic inclusion:

  if an arbitrary reconstructed vertex u can reach inl(r),
  then r lies in the canonical support of u.

Indeed all reconstructed edge clauses decrease support, and every
root-sort vertex r belongs to its own unary singleton closure.
This handles one inclusion in roots_B(u)=support(u) once the exact
root predicate has been identified; it does not assume that fact.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every root-sort vertex belongs to its intrinsic unary closure. -/
theorem reconstructed_root_mem_own_support
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (r : W) :
    r ∈ reconstructedSupport G k B (.inl r) :=
  B.mem_closureAtSet r

/-- **Path-theoretic upper bound for reachable roots:** any root-sort
endpoint of a directed path from u is already in the intrinsic
canonical support of u. This holds prior to the outdegree proof. -/
theorem faithful_reconstructed_reachable_root_mem_support
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (u : ReconstructedCarrier G k B)
    (r : W)
    (hReach :
      (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
        u (.inl r)) :
    r ∈ reconstructedSupport G k B u := by
  have hsubset :=
    faithful_reconstructed_reaches_support_antitone
      G k S B ι hFaith hReach
  exact hsubset (reconstructed_root_mem_own_support G k B r)

end AllThoseEPPA.Applications.KOrientations
