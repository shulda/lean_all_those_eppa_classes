import AllThoseEPPA.Applications.KOrientations.AuxiliaryLabelReflection
import AllThoseEPPA.Applications.KOrientations.ClosedGraphDTraceIso

/-!
# Reflection of R_P and E_P with only *relative* d-closedness

The distinguished first-stage source S is successor-closed but can fail
to be d-closed in the ambient B₀. A partial-automorphism domain U
inside S is closed in the original *d-trace* on S. It would be
incorrect to assume U is d-closed in the full ambient B₀.

The root/incoming auxiliary relation R_P or E_P, when evaluated on
root tuples all lying in U, is positive precisely when P.center
belongs to U, together with the tuple matching and edge conditions.
The crucial witness of P.center in a higher-arity d-fibre is only
used when P.center lies in S, so relative closure suffices.

These exact iff statements handle negative tuples and labels whose
centres lie outside the original source, as required by ORI-022.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

private theorem rootPattern_center_mem_of_traceClosed_tuple
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (S U : Set V) (hUS : U ⊆ S)
    (hU : (dTraceStructure G k S).IsClosed
      {x : S | x.val ∈ U})
    {n : ℕ} (P : RootPattern G k n)
    (hCenter : P.center ∈ S)
    (xs : Fin n → V)
    (hxs : ∀ i, xs i ∈ U)
    (hMatch : ∀ i, xs i = P.tuple i) :
    P.center ∈ U := by
  have htup : ∀ i, P.tuple i ∈ U := by
    intro i
    rw [← hMatch i]
    exact hxs i
  have hRoots : ∀ i, G.IsRoot k (P.tuple i) := by
    intro i
    have hi : P.tuple i ∈ G.roots k P.center := by
      rw [P.roots_eq]
      exact ⟨i, rfl⟩
    exact hi.1
  have hFiber : P.center ∈ G.dFiber k P.tuple :=
    ⟨P.positive, P.injective, hRoots, P.roots_eq⟩
  let ys : Fin n → S :=
    fun i => ⟨P.tuple i, hUS (htup i)⟩
  have hys : ∀ i, (ys i).val ∈ U := htup
  have hMem :
      (⟨P.center, hCenter⟩ : S) ∈
        (dTraceStructure G k S).func
          (DFunctionSymbol.fiber n P.positive) ys := by
    change P.center ∈ G.dFiber k P.tuple
    exact hFiber
  exact hU (DFunctionSymbol.fiber n P.positive) ys
    hys hMem

/-- Exact positive and negative R_P-tuple criterion for a domain
closed only inside the original source d-trace. -/
theorem auxiliary_root_label_iff_center_in_traceClosed
    {V : Type u} [Fintype V]
    (G : Digraph V) (k n : ℕ)
    (S U : Set V) (hUS : U ⊆ S)
    (hU : (dTraceStructure G k S).IsClosed
      {x : S | x.val ∈ U})
    (P : RootPattern G k n)
    (xs : Fin n → RootsIn G k S)
    (hxs : ∀ i, (xs i).val ∈ U) :
    (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.root P) xs ↔
      P.center ∈ U ∧ ∀ i, (xs i).val = P.tuple i := by
  change (P.center ∈ S ∧ ∀ i, (xs i).val = P.tuple i) ↔
    (P.center ∈ U ∧ ∀ i, (xs i).val = P.tuple i)
  constructor
  · intro h
    exact ⟨rootPattern_center_mem_of_traceClosed_tuple
      G k S U hUS hU P h.1
        (fun i => (xs i).val) hxs h.2, h.2⟩
  · intro h
    exact ⟨hUS h.1, h.2⟩

/-- Exact E_P relation with relative d-closedness. The first
coordinate is the incoming-edge root; the remaining coordinates
enumerate P's roots and determine membership of its centre. -/
theorem auxiliary_incoming_label_iff_center_in_traceClosed
    {V : Type u} [Fintype V]
    (G : Digraph V) (k n : ℕ)
    (S U : Set V) (hUS : U ⊆ S)
    (hU : (dTraceStructure G k S).IsClosed
      {x : S | x.val ∈ U})
    (P : RootPattern G k n)
    (xs : Fin (n + 1) → RootsIn G k S)
    (hxs : ∀ i, (xs i).val ∈ U) :
    (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.incoming P) xs ↔
      P.center ∈ U ∧ G.edge (xs 0).val P.center ∧
        (∀ i, (xs (Fin.succ i)).val = P.tuple i) := by
  change
    (P.center ∈ S ∧ G.edge (xs 0).val P.center ∧
      (∀ i, (xs (Fin.succ i)).val = P.tuple i)) ↔
    (P.center ∈ U ∧ G.edge (xs 0).val P.center ∧
      (∀ i, (xs (Fin.succ i)).val = P.tuple i))
  constructor
  · rintro ⟨hs, he, ht⟩
    have hc : P.center ∈ U :=
      rootPattern_center_mem_of_traceClosed_tuple
        G k S U hUS hU P hs
          (fun i => (xs (Fin.succ i)).val)
          (fun i => hxs (Fin.succ i)) ht
    exact ⟨hc, he, ht⟩
  · rintro ⟨hc, he, ht⟩
    exact ⟨hUS hc, he, ht⟩

end AllThoseEPPA.Applications.KOrientations
