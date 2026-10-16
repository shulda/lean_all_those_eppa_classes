import AllThoseEPPA.Applications.KOrientations.FirstStageSelectedGraphDomainImage
import AllThoseEPPA.Applications.KOrientations.GraphPermutations

/-!
# Exact reachable-root set transport under the ACTUAL first EPPA selector

The original complete all-arity d(A)-partial automorphism p induces
a true unary-successor partial map, whose real first coherent
EPPA extension f_p acts on the entire B₀ graph. The associated
full graph automorphism g_p is not posthoc chosen: it is exactly
the language component of the selected second Γ-root input.

For every original vertex x in the closed source of p,
g_p maps the entire B₀ ambient reachable-root set of ι(x)
bijectively onto the reachable-root set of ι(p(x)).
This holds even though g_p need NOT globally preserve the old
embedded subset S=ι[A], and even though S is not globally d-closed
in B₀. We use the actual first extension equation at x plus the
graph-automorphism root-set equivariance theorem.

This exact set-image equality is a prerequisite for comparing the
nonroot (centre, full support) pairs of the reconstructed witness
under the genuinely selected second auxiliary automorphism.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The selected first EPPA graph automorphism maps the complete
set of roots reachable from each original d-partial-domain
vertex x EXACTLY onto the roots reachable from its true image p x,
with genuine nonfaithful Γ language-component action. -/
theorem firstStage_selectedGraphAut_originalRootSet_image
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (x : V) (hx : x ∈ p.source) :
    (graphAutOfSuccessorAut G
      (s.extension (dPartialAutomorphism_to_successor A k p))).1 ''
        G.roots k (ι x) =
      G.roots k (ι (p x)) := by
  let f := s.extension (dPartialAutomorphism_to_successor A k p)
  let g := graphAutOfSuccessorAut G f
  have hFirst : f (ι x) = ι (p x) :=
    (s.extension_spec (dPartialAutomorphism_to_successor A k p)).2 x hx
  calc
    (graphAutOfSuccessorAut G
        (s.extension (dPartialAutomorphism_to_successor A k p))).1 ''
        G.roots k (ι x) =
      G.roots k (g.1 (ι x)) := by
        exact (G.roots_image_of_perm k g.1 g.2 (ι x)).symm
    _ = G.roots k (ι (p x)) := by
      rw [show g.1 (ι x) = ι (p x) from hFirst]

end AllThoseEPPA.Applications.KOrientations
