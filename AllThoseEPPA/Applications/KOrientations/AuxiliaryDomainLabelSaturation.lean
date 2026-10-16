import AllThoseEPPA.Applications.KOrientations.ClosedGraphDTraceIso
import AllThoseEPPA.Applications.KOrientations.AuxiliaryLanguage

/-!
# Root-labelled auxiliary relations on d-closed source domains

A crucial point in the two-stage coherent EPPA application is that
a partial root map must preserve and reflect *all* auxiliary relation
symbols, including labels whose centres lie outside the original
partial domain (and potentially outside the source S).

For a d-closed subdomain T of the canonical d-trace of S, and a
tuple of roots lying in T, an auxiliary R_P-relation is positive
exactly when the label's centre belongs to T and the ordered tuple
matches P. The analogous E_P-relation has the additional source
root-to-centre edge condition.

The forward implication is nontrivial: if all of P's roots lie in T,
its centre is forced into T by the appropriate higher-arity F_n fibre,
*provided its label is realised in the original source S*.
No assumption that S is d-closed in the ambient first-stage witness
is made, and negative tuples/labels outside S are covered.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- A realised R_P-tuple in a domain closed under the intrinsic
d-trace forces the corresponding nonroot centre into that domain. -/
theorem closed_dTrace_aux_root_center_mem
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T : Set S)
    (hT : (dTraceStructure G k S).IsClosed T)
    {n : ℕ} (P : RootPattern G k n)
    (xs : Fin n → RootsIn G k S)
    (hRel : (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.root P) xs)
    (hxs : ∀ i : Fin n,
      (⟨(xs i).val, (xs i).property.1⟩ : S) ∈ T) :
    (⟨P.center, hRel.1⟩ : S) ∈ T := by
  let ys : Fin n → S :=
    fun i => ⟨(xs i).val, (xs i).property.1⟩
  have hTuple : (fun i : Fin n => (ys i).val) = P.tuple := by
    funext i
    exact hRel.2 i
  have hRoot : ∀ i, G.IsRoot k (P.tuple i) := by
    intro i
    have hi : P.tuple i ∈ G.roots k P.center := by
      rw [P.roots_eq]
      exact ⟨i, rfl⟩
    exact hi.1
  have hFiber :
      P.center ∈ G.dFiber k (fun i : Fin n => (ys i).val) := by
    rw [hTuple]
    exact ⟨P.positive, P.injective, hRoot, P.roots_eq⟩
  have hValue :
      (⟨P.center, hRel.1⟩ : S) ∈
        (dTraceStructure G k S).func
          (DFunctionSymbol.fiber n P.positive) ys := hFiber
  exact hT (DFunctionSymbol.fiber n P.positive) ys hxs hValue

/-- Full reflection of arbitrary root-labelled relations on a
d-trace-closed domain, including externally indexed patterns. -/
theorem closed_dTrace_aux_root_rel_iff
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T : Set S)
    (hT : (dTraceStructure G k S).IsClosed T)
    {n : ℕ} (P : RootPattern G k n)
    (xs : Fin n → RootsIn G k S)
    (hxs : ∀ i : Fin n,
      (⟨(xs i).val, (xs i).property.1⟩ : S) ∈ T) :
    (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.root P) xs ↔
      (P.center ∈ Subtype.val '' T) ∧
        ∀ i : Fin n, (xs i).val = P.tuple i := by
  constructor
  · intro hRel
    refine ⟨?_, hRel.2⟩
    exact ⟨⟨P.center, hRel.1⟩,
      closed_dTrace_aux_root_center_mem G k S T hT P xs hRel hxs,
      rfl⟩
  · rintro ⟨⟨c, hc, heq⟩, hTuple⟩
    refine ⟨?_, hTuple⟩
    rw [← heq]
    exact c.property

/-- Incoming-labelled tuples obey the same centre-saturation rule,
with their additional directed edge condition. -/
theorem closed_dTrace_aux_incoming_rel_iff
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T : Set S)
    (hT : (dTraceStructure G k S).IsClosed T)
    {n : ℕ} (P : RootPattern G k n)
    (xs : Fin (n+1) → RootsIn G k S)
    (hxs : ∀ i : Fin (n+1),
      (⟨(xs i).val, (xs i).property.1⟩ : S) ∈ T) :
    (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.incoming P) xs ↔
      (P.center ∈ Subtype.val '' T) ∧
      G.edge (xs 0).val P.center ∧
      (∀ i : Fin n,
        (xs (Fin.succ i)).val = P.tuple i) := by
  let tail : Fin n → RootsIn G k S :=
    fun i => xs (Fin.succ i)
  have htail : ∀ i : Fin n,
      (⟨(tail i).val, (tail i).property.1⟩ : S) ∈ T :=
    fun i => hxs (Fin.succ i)
  constructor
  · intro hRel
    have hRootRel : (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.root P) tail :=
      ⟨hRel.1, hRel.2.2⟩
    have hCenter := (closed_dTrace_aux_root_rel_iff
      G k S T hT P tail htail).mp hRootRel
    exact ⟨hCenter.1, hRel.2.1, hRel.2.2⟩
  · rintro ⟨⟨c, hc, heq⟩, hedge, hTuple⟩
    refine ⟨?_, hedge, hTuple⟩
    rw [← heq]
    exact c.property

end AllThoseEPPA.Applications.KOrientations
