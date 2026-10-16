import AllThoseEPPA.Applications.KOrientations.AuxiliaryClosedRootTransport

/-!
# All auxiliary relations on a d-closed root domain

Combine the exact reflected R_P and E_P statements, including
externally indexed patterns, with ordinary graph-edge equivariance.
The result treats the entire arity-indexed auxiliary relation
language in a single uniform statement.

The remaining partial-isomorphism construction must also transport
the auxiliary unary function and totalize the domain-restricted
vertex equivalence as a PartialEquiv.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- The full auxiliary relation language is preserved and reflected,
not merely preserved, on matching closed root-domain tuples. -/
theorem closed_dTrace_aux_relation_transport_iff
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T T' : Set S)
    (hT : (dTraceStructure G k S).IsClosed T)
    (hT' : (dTraceStructure G k S).IsClosed T')
    (g : G.graphAut)
    (hImage : g.1 '' (Subtype.val '' T) = Subtype.val '' T')
    {n : ℕ} (R : AuxiliaryRel G k n)
    (xs ys : Fin n → RootsIn G k S)
    (hxs : ∀ i, (⟨(xs i).val, (xs i).property.1⟩ : S) ∈ T)
    (hys : ∀ i, (⟨(ys i).val, (ys i).property.1⟩ : S) ∈ T')
    (hxy : ∀ i, (ys i).val = g.1 (xs i).val) :
    (auxiliaryRootStructure G k S).rel R xs ↔
      (auxiliaryRootStructure G k S).rel
        ((auxiliaryAction G k).onRel g R) ys := by
  cases R with
  | edge =>
      change G.edge (xs 0).val (xs 1).val ↔
        G.edge (ys 0).val (ys 1).val
      simpa only [hxy 0, hxy 1] using
        (g.2 (xs 0).val (xs 1).val).symm
  | root P =>
      exact closed_dTrace_root_relation_transport_iff
        G k S T T' hT hT' g hImage P xs ys hxs hys hxy
  | incoming P =>
      exact closed_dTrace_incoming_relation_transport_iff
        G k S T T' hT hT' g hImage P xs ys hxs hys hxy

end AllThoseEPPA.Applications.KOrientations
